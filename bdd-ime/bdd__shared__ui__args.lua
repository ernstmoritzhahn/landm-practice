-- ui/args.lua -- command-line parsing shared by the SDL and KMS
-- frontends (the former nkl_parse_args in nkl.c).  The C frontend calls
-- args.parse through the ui_parse_args hook once nkl_lua_init() has
-- run; failures come back as nil + a ready-made message which C prints
-- as "prog: <msg>\nTry 'prog --help' ..." before exiting 2.
--
-- Same dialect rule as the rest of the UI (LuaJIT intersect Lua 5.4).
local args = {}

local function die(msg)
    return nil, msg
end

-- "--name" or "--name=value"; on a match returns true plus the inline
-- value (possibly "" for "--name="), otherwise false
local function opt_eq(a, name)
    if a:sub(1, #name) ~= name then return false end
    local rest = a:sub(#name + 1)
    if rest == "" then return true, nil end
    if rest:sub(1, 1) == "=" then return true, rest:sub(2) end
    return false
end

-- the value of an option: its inline `=value` when present, else the
-- next argv token — which must exist and not itself be an option
local function opt_value(argv, i, inl)
    if inl ~= nil then return inl, i end
    local v = argv[i + 1]
    if v == nil or v:sub(1, 2) == "--" then
        return nil, i, "option requires a value: " .. argv[i]
    end
    return v, i + 1
end

local function opt_long(opt, v, lo, hi)
    -- strtol semantics: optional leading whitespace and sign, digits
    -- only — "0x10"/"4.5"/"1e3"/"42 " fail where tonumber would accept
    if not v:match("^%s*[+-]?%d+$") then
        return nil, string.format(
            "invalid value for %s: '%s' (want %d..%d)", opt, v, lo, hi)
    end
    local n = tonumber(v)
    if not n or n < lo or n > hi then
        return nil, string.format(
            "invalid value for %s: '%s' (want %d..%d)", opt, v, lo, hi)
    end
    return n
end

-- argv[1..] are the option tokens (the program name is handled C-side);
-- `desktop` marks the SDL frontend — the window options and the FONT
-- positional only exist there, the KMS build rejects them.
-- `cap` lets sibling apps (automata-ime) shrink the grammar to what
-- makes sense for them: {server=false} drops --host/--port/--model,
-- {features=false} drops --features, {font=false} drops the FONT
-- positional.  Missing fields default to true.
function args.parse(argv, desktop, cap)
    cap = cap or {}
    local has_server   = cap.server   ~= false
    local has_features = cap.features ~= false
    local has_font     = cap.font     ~= false
    local r = {
        auto_server = has_server,
        help = false,
        host = has_server and "127.0.0.1" or nil,
        port = has_server and (cap.port or 9001) or nil,
        model = nil,
        width = 0,
        height = 0,
        fullscreen = false,
        resizable = false,
        features = nil,
        font = nil,
    }
    local end_of_opts = false
    local i = 1
    while argv[i] ~= nil do
        local a = argv[i]
        local inl
        local function opt(name)
            local m
            m, inl = opt_eq(a, name)
            return m
        end
        if end_of_opts or a:sub(1, 1) ~= "-" or a == "-" then
            -- positional: the SDL build reads it as the CJK font path
            if not desktop or not has_font then
                return die("unexpected argument: " .. a) end
            if r.font then return die("unexpected extra argument: " .. a) end
            r.font = a
        elseif a == "--" then
            end_of_opts = true
        elseif has_server and opt("--host") then
            local v, ni, err = opt_value(argv, i, inl)
            if err then return die(err) end
            if v == "" then return die("empty value for --host") end
            r.host, i, r.auto_server = v, ni, false
        elseif has_server and opt("--port") then
            local v, ni, err = opt_value(argv, i, inl)
            if err then return die(err) end
            local n; n, err = opt_long("--port", v, 1, 65535)
            if not n then return die(err) end
            r.port, i, r.auto_server = n, ni, false
        elseif has_server and opt("--model") then
            local v, ni, err = opt_value(argv, i, inl)
            if err then return die(err) end
            if v == "" then return die("empty value for --model") end
            r.model, i = v, ni
        elseif desktop and opt("--width") then
            local v, ni, err = opt_value(argv, i, inl)
            if err then return die(err) end
            local n; n, err = opt_long("--width", v, 1, 16384)
            if not n then return die(err) end
            r.width, i = n, ni
        elseif desktop and opt("--height") then
            local v, ni, err = opt_value(argv, i, inl)
            if err then return die(err) end
            local n; n, err = opt_long("--height", v, 1, 16384)
            if not n then return die(err) end
            r.height, i = n, ni
        elseif desktop and a == "--fullscreen" then
            r.fullscreen = true
        elseif desktop and a == "--resizable" then
            r.resizable = true
        elseif has_features and opt("--features") then
            local v, ni, err = opt_value(argv, i, inl)
            if err then return die(err) end
            r.features, i = v, ni
        elseif a == "--help" or a == "-h" then
            r.help = true
        else
            return die("unknown option: " .. a)
        end
        i = i + 1
    end
    return r
end

return args
