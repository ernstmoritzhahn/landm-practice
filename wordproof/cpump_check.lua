-- wordproof/cpump_check.lua — pumping lemma for context-free
-- languages.  The student supplies z(k) as a block list (e.g.
-- "a^k b^k c^k d^k", exponents may be expressions in k incl. k*k)
-- and a pumping index i for every declared case.  The checker
-- enumerates all legal splits z=uvwxy (|vwx|<=k, |vx|>0) for
-- k=2,3, assigns each to a case via the task's matchers, and
-- verifies uv^iwx^iy not in L concretely via part.lang_test.
-- part = { kind="cpump", alphabet, cases={{id,desc,match}}, z_hint,
--          zgen=fn (fixed z for irregular witnesses), lang_test=fn,
--          i_cases = number of i fields }
local util = require "lib.util"
local trim = util.trim

local M = {}

-- tiny expression evaluator: numbers, identifiers, + - * / ^ ( )
local function eval_exp(src, env)
    -- implicit multiplication: 2k, 3m, k(k+1)
    src = tostring(src):gsub("(%d)(%a)", "%1*%2")
        :gsub("(%a)(%d)", "%1*%2")
        :gsub("%)(%a)", ")*%1")
        :gsub("(%a)%(", "%1*(")
        :gsub("%)%(", ")*(")
    local pos, s = 1, src
    local function peek() return s:sub(pos, pos) end
    local function skip() while s:sub(pos,pos):match("%s") do
        pos = pos + 1 end end
    local expr
    local function atom()
        skip()
        local c = peek()
        if c == "(" then
            pos = pos + 1
            local v = expr()
            skip(); pos = pos + 1
            return v
        end
        local num = s:match("^%d+", pos)
        if num then pos = pos + #num return tonumber(num) end
        local id = s:match("^%a+", pos)
        if id then pos = pos + #id
            return env[id] or error("unknown name '" .. id .. "'")
        end
        error("bad expression '" .. s .. "'")
    end
    local function pow()
        local v = atom()
        skip()
        if peek() == "^" then
            pos = pos + 1
            local e = atom()
            return v ^ e
        end
        return v
    end
    local function term()
        local v = pow()
        while true do
            skip()
            local c = peek()
            if c == "*" then pos = pos + 1 v = v * pow()
            elseif c == "/" then pos = pos + 1 v = v / pow()
            else return v end
        end
    end
    expr = function()
        local v = term()
        while true do
            skip()
            local c = peek()
            if c == "+" then pos = pos + 1 v = v + term()
            elseif c == "-" then pos = pos + 1 v = v - term()
            else return v end
        end
    end
    local v = expr()
    skip()
    if pos <= #s then error("trailing '" .. s:sub(pos) .. "'") end
    return v
end
M.eval_exp = eval_exp

-- z(k) block list:  a^k b^{2k} a^{k*k} (a)^k ...
-- returns function k -> word string, or nil,err
function M.parse_z(text)
    local blocks = {}
    local s = (text or ""):gsub("%s+", "")
    local i = 1
    while i <= #s do
        local sym
        if s:sub(i,i) == "(" then
            local close = s:find(")", i, true)
            if not close then return nil, "unclosed '(' in z(k)" end
            sym = s:sub(i + 1, close - 1)
            i = close + 1
        else
            sym = s:sub(i, i)
            i = i + 1
        end
        local exp = "1"
        if s:sub(i,i) == "^" then
            i = i + 1
            if s:sub(i,i) == "{" then
                local close = s:find("}", i, true)
                if not close then
                    return nil, "unclosed '{' in z(k)"
                end
                exp = s:sub(i + 1, close - 1)
                i = close + 1
            elseif s:sub(i,i) == "(" then
                local close = s:find(")", i, true)
                exp = s:sub(i + 1, close - 1)
                i = close + 1
            else
                exp = s:match("^[k0-9%+%-%*/^]+", i)
                i = i + #exp
            end
        end
        blocks[#blocks + 1] = { sym = sym, exp = exp }
    end
    if #blocks == 0 then return nil, "empty z(k)" end
    return function(k)
        local w = {}
        for _, b in ipairs(blocks) do
            local e = eval_exp(b.exp, { k = k })
            e = math.floor(e + 0.5)
            if e < 0 then return nil end
            w[#w + 1] = b.sym:rep(e)
        end
        return table.concat(w)
    end
end

-- enumerate all legal splits of zw = u v w x y (|vwx|<=k, |vx|>0);
-- v and x may be empty, w may be empty
local function each_split(zw, k, fn)
    local n = #zw
    for ws = 1, n do                       -- window start (vwx)
        for we = ws, math.min(n, ws + k - 1) do
            for vend = ws - 1, we do       -- v = zw[ws..vend]
                for xs = vend + 1, we + 1 do  -- x = zw[xs..we]
                    local v = zw:sub(ws, vend)
                    local w = zw:sub(vend + 1, xs - 1)
                    local x = zw:sub(xs, we)
                    if #v + #x > 0 then
                        fn { u = zw:sub(1, ws - 1), v = v, w = w,
                             x = x, y = zw:sub(we + 1) }
                    end
                end
            end
        end
    end
end
M.each_split = each_split

local function eval_i(expr, env)
    local ok, v = pcall(eval_exp, expr, env)
    if not ok then return nil, tostring(v) end
    v = math.floor(v + 0.5)
    if v < 0 then return nil, "i must be ≥ 0" end
    return v
end

function M.check_cpump(part, z_text, i_map)
    local lang_test = part.lang_test
    local zfn
    if part.zgen then
        zfn = part.zgen
    else
        local err
        zfn, err = M.parse_z(z_text)
        if not zfn then
            return { ok = false, msg = "z(k): " .. err }
        end
    end
    -- witness validity: z(k) ∈ L and |z| ≥ k
    for k = 2, 4 do
        local zw = zfn(k)
        if not zw or not lang_test(zw) then
            return { ok = false, msg = string.format(
                "z(%d) = '%s' is not in L — choose a witness in the "
                .. "language", k, tostring(zw)) }
        end
        if #zw < k then
            return { ok = false, msg = string.format(
                "|z(%d)| = %d < %d — need |z| ≥ k", k, #zw, k) }
        end
    end
    local nsplits, matched, ncases = 0, {}, 0
    for k = 2, 3 do
        local zw = zfn(k)
        local bad
        each_split(zw, k, function(sp)
            if bad then return end
            nsplits = nsplits + 1
            local ci
            for idx, c in ipairs(part.cases) do
                if c.match(sp, zw, k) then ci = idx break end
            end
            if not ci then
                bad = "no case covers v='" .. sp.v .. "', x='"
                    .. sp.x .. "' (z=" .. zw .. ", k=" .. k .. ")"
                return
            end
            matched[ci] = true
            local expr = i_map and i_map[ci]
            if not expr or trim(expr) == "" then
                bad = "no pumping index given for case " .. ci
                return
            end
            local i, ierr = eval_i(expr,
                { k = k, m = #sp.v, n = #sp.x })
            if not i then
                bad = "case " .. ci .. ": i — " .. ierr
                return
            end
            local pumped = sp.u .. sp.v:rep(i) .. sp.w
                .. sp.x:rep(i) .. sp.y
            if lang_test(pumped) then
                bad = string.format(
                    "case %d: i=%d keeps uv^iwx^iy in L — "
                    .. "counterexample z='%s', v='%s', x='%s' gives "
                    .. "'%s'", ci, i, zw, sp.v, sp.x, pumped)
            end
        end)
        if bad then return { ok = false, msg = bad } end
    end
    for idx in ipairs(part.cases) do
        if matched[idx] then ncases = ncases + 1 end
    end
    return { ok = true, msg = "✓ verified for all " .. nsplits
        .. " legal decompositions with k ≤ 3 (" .. ncases
        .. " case(s) exercised) — your z and indices cover every "
        .. "possibility" }
end

return M
