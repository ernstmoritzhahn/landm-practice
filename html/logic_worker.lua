-- Formula-input demonstrator worker: parses and lays out formulas,
-- answers {what="parse", input=...} messages.  Same code path the
-- future exercise/exam checkers will take (logic/ is the shared
-- backend).

local util = require "lib.util"
util.fix_path()
local json = require "lib.json"
local logic = require "logic"

local function classify(ast, info)
    local pred = false
    local function w(n)
        if n.type == "quant" then
            pred = true
            w(n.body)
        elseif n.type == "atom" then
            if #n.args > 0 then pred = true end
        elseif n.type == "op" then
            for _, a in ipairs(n.args) do w(a) end
        end
    end
    w(ast)
    return pred and "predicate" or "propositional"
end

return function(data)
    local msg = json.decode(data)
    if msg.what == "parse" then
        -- continuations for the text before the caret
        local suggestions = logic.suggest(msg.prefix or "")
        local ast, err, info = logic.parse(msg.input or "")
        if ast then
            local out = {
                ok = true,
                render = logic.render(ast),
                kind = classify(ast, info),
                free = info.free,
                closed = #info.free == 0,
                layout = logic.layout(ast),
                ast = ast,
                suggestions = suggestions,
            }
            util.js_post_message(json.encode(out))
        else
            util.js_post_message(json.encode({
                ok = false,
                message = err.message,
                pos = err.pos,
                expected = err.expected,
                suggestions = suggestions,
            }))
        end
    end
end
