-- server/service.lua — automaton-server request dispatch, the same
-- shape as the BayesL service: a factory that takes the json module
-- and returns a function payload -> response payload.  Methods:
--
--   {method="report", seq=N, model={...}, checks={key=bool,...}}
--       -> {method="report", seq=N, problems=[...]}
--          (problems from checks.run over the supplied — or last
--           received — model; enabled checks come from `checks`)
--   {method="get_model"} -> {method="model", model={...}|nil}
--          (the last reported/restored model — lets a --model file
--           be pulled back by a connecting client)
--   {method="set_model", model={...}} -> {method="ok"}
--
-- Unknown methods get {method="error", msg=...}; a malformed frame
-- returns the same shape so the client never waits on a parse error.

local checks = require "checks"

local M = {}

function M.new(json)
    local current = nil      -- last model the client reported

    local function dispatch(payload)
        local ok, obj = pcall(json.decode, payload)
        if not ok or type(obj) ~= "table" then
            return json.encode{method = "error",
                               msg = "malformed request"}
        end
        local meth = obj.method
        if meth == "report" then
            if type(obj.model) == "table" then current = obj.model end
            local problems = checks.run(current or {},
                                        type(obj.checks) == "table"
                                        and obj.checks or nil)
            return json.encode{method = "report", seq = obj.seq,
                               problems = problems}
        elseif meth == "set_model" then
            if type(obj.model) == "table" then current = obj.model end
            return json.encode{method = "ok"}
        elseif meth == "get_model" then
            return json.encode{method = "model", model = current}
        end
        return json.encode{method = "error",
                           msg = "unknown method: " .. tostring(meth)}
    end
    return dispatch
end

return M
