-- ui/api.lua — the nkl_api C bridge as a require-able module.
--
-- The C side hands the function-pointer table to ui.lua's ui_set_api(),
-- which wraps it in a proxy (NULL function pointers filtered out) and
-- calls api.set() once.  Modules then do
--
--     local A = require "ui.api"
--     A.row(...)
--
-- Field access resolves at call time, so modules may be required before
-- ui_set_api() runs.  `set` is the module's only own field; a NULL
-- bridge pointer reads back as nil (same coercion ui.lua applies).

local real
local M = setmetatable({}, {__index = function(_, k)
    if not real then return nil end
    local f = real[k]
    if f == nil then return nil end   -- NULL fnptr cdata -> real nil
    return f
end})

function M.set(api) real = api end

-- ui_set_api() bootstrap, shared by every entry point (ui.lua files):
-- wraps the const struct nkl_api* the C side passes as lightuserdata in
-- a caching proxy (NULL function pointers filtered out — a NULL cdata
-- compares equal to nil but is still a cdata) and publishes it through
-- M.set().  luaffifb may reject lightuserdata casts, so the hex address
-- fallback stays.  The PROXY (not the raw cdata) must be what callers
-- see: under luaffifb every struct-field read mints a new function
-- cdata and the ffi.c closure cache keys on it — an uncached read would
-- recompile a closure on EVERY bridge call.
function M.bind(p, hex)
    local ffi = require "ffi"
    local ok, api = pcall(ffi.cast, "const struct nkl_api*", p)
    if (not ok or api == nil) and hex then
        api = ffi.cast("const struct nkl_api*", tonumber(hex, 16))
    end
    local proxy = setmetatable({}, {
        __index = function(t, k)
            local f = api[k]
            if f == nil then f = nil end
            t[k] = f
            return f
        end
    })
    ui_api_cache = proxy
    M.set(proxy)
    return proxy
end

return M
