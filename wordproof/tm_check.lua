-- wordproof/tm_check.lua — check student Turing machines entered as
-- transition lists (Sudkamp "standard" TMs, generalised to k tapes).
--   start: q0            final: q3 qf
--   q0, a X R, q1        (read a, write X, move R, go to q1)
--   q1, b b R | ⊔ ⊔ L, q2    (tape-2 slot after '|')
-- Semantics: one-way-infinite tapes, blank ⊔ (B also accepted), input on tape 1 at
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
        if r == "⊔" then r = "B" end   -- internal blank cell
        if r == "λ" or r == "ε" then
            return nil, "λ is not the blank — use ⊔"
        end
        if w == "⊔" then w = "B" end
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

-- Sudkamp determinism: two transitions from the same state conflict
-- when their read tuples are identical on every tape
local function is_deterministic(tm)
    for st, list in pairs(tm.trans) do
        local seen = {}
        for _, tr in ipairs(list) do
            local reads = {}
            for t = 1, tm.ntapes do reads[#reads + 1] = tr.tapes[t].r end
            local key = table.concat(reads, "|")
            if seen[key] then
                return false, string.format(
                    "nondeterministic in state %s: two transitions "
                    .. "read '%s'", st, key)
            end
            seen[key] = true
        end
    end
    return true
end

local function check_tm_obj(part, tm, atype)
    -- tm|tm-N is the deterministic family (part.deterministic makes a
    -- legacy part demand it too); ntm* branches freely
    local label_lang = require "automata.label_lang"
    local want_det = part.deterministic
                     or (label_lang.is_det_tm
                         and label_lang.is_det_tm(
                             part.aut_type or atype or "tm"))
    if want_det then
        local det, derr = is_deterministic(tm)
        if not det then
            return { ok = false,
                     msg = derr
                         .. " — the TM must be deterministic" }
        end
    end
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

function M.check_tm(part, text)
    local tm, err = M.parse_tm_text(text, part.tapes or 1)
    if not tm then return { ok = false, msg = err } end
    return check_tm_obj(part, tm)
end

-- graphical input: the editor's model JSON; each transition label
-- parses through automata.label_lang as 'read write L|R|S', '|'-
-- separated per tape on multitape types ("tm-2" → ntapes=2)
function M.check_tm_model(part, model_json)
    local json = require "lib.json"
    local label_lang = require "automata.label_lang"
    local ok, m = pcall(json.decode, model_json or "")
    if not ok or type(m) ~= "table" or not m.states
       or #m.states == 0 then
        return { ok=false, msg="no automaton — draw the state diagram" }
    end
    local ntapes = label_lang.tapes(m.type) or part.tapes or 1
    local tm = { trans = {}, finals = {}, ntapes = ntapes }
    local names, problems = {}, {}
    for _, s in ipairs(m.states) do
        local nm = tostring(s.name or s.id)
        names[s.id] = nm
        if s.initial then
            if tm.start then
                problems[#problems + 1] = "more than one initial state"
            else
                tm.start = nm
            end
        end
        if s.accepting then tm.finals[nm] = true end
    end
    for _, e in ipairs(m.transitions or {}) do
        local a, b = names[e.from], names[e.to]
        if not (a and b) then
            problems[#problems + 1] = "transition with a dangling "
                .. "endpoint"
        else
            local ts, why = label_lang.parse_many(
                label_lang.tapes(m.type) and m.type
                    or ("tm" .. (ntapes > 1 and ("-" .. ntapes) or "")),
                e.label)
            if not ts then
                problems[#problems + 1] = "label '" .. tostring(e.label)
                    .. "': " .. why
            else
                for _, t in ipairs(ts) do
                    local tapes = {}
                    for i, c in ipairs(t) do
                        tapes[i] = { r = c[1], w = c[2], d = c[3] }
                    end
                    local l = tm.trans[a] or {}
                    tm.trans[a] = l
                    l[#l + 1] = { from = a, tapes = tapes, to = b }
                end
            end
        end
    end
    if not tm.start then
        problems[#problems + 1] = "no initial state"
    end
    if #problems > 0 then
        return { ok = false, msg = table.concat(problems, "; ") }
    end
    return check_tm_obj(part, tm, m.type)
end

return M
