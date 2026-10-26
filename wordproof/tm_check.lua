-- wordproof/tm_check.lua — check student Turing machines entered as
-- transition lists (Sudkamp "standard" TMs, generalised to k tapes).
--   start: q0            final: q3 qf
--   q0, a X R, q1        (read a, write X, move R, go to q1)
--   q1, b b R | B B L, q2    (tape-2 slot after '|')
-- Semantics: one-way-infinite tapes, blank B, input on tape 1 at
-- positions 0..n-1, all heads at position 0.  A machine halts when no
-- transition applies; it accepts iff it halts in a final state.
-- Nondeterministic machines are explored by BFS (config cap).
-- part = { kind="tm", accept={words}, reject={words}, tapes=n,
--          tape1_no_L=bool, max_steps }
local util = require "lib.util"
local trim, split = util.trim, util.split

local M = {}

local function parse_line(line)
    local key, rest = line:match("^(%a+)%s*:%s*(.-)%s*$")
    if key then return { decl = key:lower(), rest = rest } end
    local from, mid, to =
        line:match("^(.-)%s*[,;]%s*(.-)%s*[,;]%s*(.-)%s*$")
    if not from then
        return nil, "expected 'state, read write move [| ...], state'"
    end
    local tapes = {}
    for slot in (trim(mid) .. "|"):gmatch("(.-)%|") do
        local r, w, d = trim(slot):match("^(%S+)%s+(%S+)%s+([LRS])")
        if not r then
            return nil, "bad tape clause '" .. trim(slot)
                .. "' (want 'read write L|R|S')"
        end
        if r == "λ" then r = "B" end
        if w == "λ" or w == "~" then w = nil end  -- ~: keep symbol
        tapes[#tapes + 1] = { r = r, w = w, d = d }
    end
    return { from = trim(from), tapes = tapes, to = trim(to) }
end

function M.parse_tm_text(text, ntapes)
    local tm = { trans = {}, finals = {}, ntapes = ntapes or 1 }
    local err
    for _, raw in ipairs(split(text or "", "\n")) do
        local line = trim(raw:gsub("%-%-.*$", ""))
        if line ~= "" then
            local t, perr = parse_line(line)
            if not t then err = "line '" .. line .. "': " .. perr
            elseif t.decl then
                if t.decl == "start" or t.decl == "initial" then
                    tm.start = trim((split(t.rest, "%s")[1]))
                elseif t.decl == "final" or t.decl == "accept"
                        or t.decl == "accepting" then
                    for _, s in ipairs(split(t.rest, "[%s,]+")) do
                        if trim(s) ~= "" then
                            tm.finals[trim(s)] = true
                        end
                    end
                else err = "unknown declaration '" .. t.decl .. ":'"
                end
            else
                if #t.tapes ~= tm.ntapes then
                    err = "line '" .. line .. "': expected "
                        .. tm.ntapes .. " tape clause(s)"
                else
                    local l = tm.trans[t.from] or {}
                    tm.trans[t.from] = l
                    l[#l + 1] = t
                end
            end
        end
        if err then return nil, err end
    end
    if not tm.start then
        return nil, "no start state declared (add a 'start: q0' line)"
    end
    return tm
end

local function conf_key(c)
    local parts = { c.state }
    for t = 1, c.ntapes do
        parts[#parts + 1] = tostring(c.pos[t]) .. ":"
            .. table.concat(c.tape[t], ",")
    end
    return table.concat(parts, "|")
end

-- BFS simulate; returns "accept" | "reject" | "timeout"
function M.run(tm, word, max_steps)
    local function fresh_conf()
        local c = { state = tm.start, ntapes = tm.ntapes,
                    pos = {}, tape = {} }
        for t = 1, tm.ntapes do
            c.pos[t] = 0
            c.tape[t] = {}
            if t == 1 then
                for i = 1, #word do c.tape[1][i - 1] = word:sub(i, i) end
            end
        end
        return c
    end
    local queue, seen, steps = { fresh_conf() }, {}, 0
    while #queue > 0 and steps < (max_steps or 8000) do
        local c = table.remove(queue, 1)
        steps = steps + 1
        local list = tm.trans[c.state]
        local moved = false
        if list then
            for _, tr in ipairs(list) do
                local ok = true
                for t = 1, tm.ntapes do
                    local cur = c.tape[t][c.pos[t]] or "B"
                    if tr.tapes[t].r ~= cur then ok = false break end
                end
                if ok then
                    moved = true
                    local n = { state = tr.to, ntapes = c.ntapes,
                                pos = {}, tape = {} }
                    for t = 1, c.ntapes do
                        n.tape[t] = {}
                        for k, v in pairs(c.tape[t]) do
                            n.tape[t][k] = v
                        end
                        local p = c.pos[t]
                        if tr.tapes[t].w then
                            n.tape[t][p] = tr.tapes[t].w
                        end
                        if tr.tapes[t].d == "R" then p = p + 1
                        elseif tr.tapes[t].d == "L" then
                            p = math.max(0, p - 1)
                        end
                        n.pos[t] = p
                    end
                    local key = conf_key(n)
                    if not seen[key] then
                        seen[key] = true
                        queue[#queue + 1] = n
                    end
                end
            end
        end
        if not moved then
            return tm.finals[c.state] and "accept" or "reject"
        end
    end
    return "timeout"
end

function M.check_tm(part, text)
    local tm, err = M.parse_tm_text(text, part.tapes or 1)
    if not tm then return { ok = false, msg = err } end
    if part.tape1_no_L then
        for st, list in pairs(tm.trans) do
            for _, tr in ipairs(list) do
                if tr.tapes[1].d == "L" then
                    return { ok = false, msg = "tape 1 may only move "
                        .. "R or S ('" .. st .. "' uses L)" }
                end
            end
        end
    end
    local bad, npos = {}, 0
    for _, w in ipairs(part.accept or {}) do
        npos = npos + 1
        if M.run(tm, w, part.max_steps) ~= "accept" then
            bad[#bad + 1] = "'" .. (w == "" and "λ" or w)
                .. "' should be accepted but is not"
            if #bad >= 2 then break end
        end
    end
    for _, w in ipairs(part.reject or {}) do
        if M.run(tm, w, part.max_steps) == "accept" then
            bad[#bad + 1] = "'" .. (w == "" and "λ" or w)
                .. "' is accepted but not in the language"
            if #bad >= 2 then break end
        end
    end
    if #bad > 0 then
        return { ok = false, msg = table.concat(bad, "; ") }
    end
    return { ok = true, msg = "✓ correct on all "
        .. (npos + #(part.reject or {})) .. " test words"
        .. (tm.ntapes > 1 and (" (" .. tm.ntapes .. " tapes)") or "") }
end

return M
