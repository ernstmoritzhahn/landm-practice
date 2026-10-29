-- server/checks.lua — the automaton consistency checks: a MODULAR
-- registry of independent checks, each a {key, name, sev, run} spec
-- returning zero or more problems.  Pure Lua (no ffi): the same file
-- runs server-side (spawned child, see server.lua) and client-side
-- (the properties column builds its toggle list from checks.specs),
-- so the check catalogue lives in exactly one place.
--
-- Model shape (what the client sends, mirrors ui/aut/model.to_table):
--   {type   = "dfa"|"nfa",           -- more types register later
--    alphabet = "a,b",               -- may be "" = unspecified
--    states      = { {id, name, initial, accepting}, ... },
--    transitions = { {id, from, to, label}, ... }}
--
-- Every problem is {sev="error"|"warning", key=<check key>, msg=...,
-- node=<state id>?, edge=<transition id>?} — the GUI maps node/edge
-- ids onto canvas colouring and message lists, exactly like the
-- BayesL report protocol.

local M = {}

-- structured transition-label grammars (PDA, TM): shared LPeg module
-- from teaching/lua/automata.  Optional — without it the typed-label
-- checks degrade to non-empty checks only.
local has_ll, label_lang = pcall(require, "automata.label_lang")
if not has_ll then label_lang = nil end

-- every type the editor knows: finite automata plus the structured-
-- label machines — the PDA family (pda|pda-f|pda-e nondeterministic,
-- dpda* deterministic; the suffix selects the acceptance mode) and
-- the TM family (tm|tm-N deterministic, ntm|ntm-N nondeterministic)
function M.is_known_type(t)
    if type(t) ~= "string" then return false end
    return t == "dfa" or t == "dfa-part" or t == "nfa"
           or t == "nfa-eps"
           or t == "pda" or t == "pda-f" or t == "pda-e"
           or t == "dpda" or t == "dpda-f" or t == "dpda-e"
           or t == "tm" or t == "ntm"
           or t:match("^n?tm%-%d+$") ~= nil
end

-- ---------------------------------------------------------------
-- symbol/alphabet parsing (shared vocabulary for the label checks)

-- "a,b" -> {"a","b"}; "ab" (no separators) -> {"a","b"} per-symbol
-- chars; "0 1" -> {"0","1"}.  Returns list + set, or nil on empty.
local function parse_alphabet(str)
    str = (str or ""):gsub("^%s+", ""):gsub("%s+$", "")
    if str == "" then return nil end
    local list, set = {}, {}
    if str:find(",") or str:find("%s") then
        for tok in str:gmatch("[^,%s]+") do
            if tok ~= "" and not set[tok] then
                set[tok] = true
                list[#list + 1] = tok
            end
        end
    else
        for i = 1, #str do
            local c = str:sub(i, i)
            if not set[c] then set[c] = true; list[#list + 1] = c end
        end
    end
    if #list == 0 then return nil end
    return list, set
end
M.parse_alphabet = parse_alphabet

-- a transition label is a comma-separated symbol list: "a", "a,b",
-- "0,1".  "" (unlabelled) is an ERROR on every type — epsilon is
-- written explicitly as λ (typed as \lambda, the editor converts it;
-- ε is NOT used — the lecture's empty-word symbol is λ).  Only NFA-λ
-- accepts it.  Returns the symbol list plus eps flag; malformed
-- lists (empty part: "a,,b", trailing ",", whole empty label)
-- return nil, reason.
local EPS_WORDS = {["λ"] = true}
local function parse_label(label)
    label = label or ""
    if label:match("^%s*$") then return nil, "empty label" end
    local syms, eps = {}, false
    for part in (label .. ","):gmatch("(.-),") do
        local t = part:gsub("^%s+", ""):gsub("%s+$", "")
        if t == "" then
            return nil, "empty symbol in label"
        elseif EPS_WORDS[t] then
            eps = true
        else
            syms[#syms + 1] = t
        end
    end
    return syms, eps
end
M.parse_label = parse_label

-- deterministic types: the plain DFA and the explicitly incomplete
-- ("partial") variant — both reject nondeterminism and epsilon;
-- only the plain one is totality-checked
local function is_dfa(t) return t == "dfa" or t == "dfa-part" end

-- ---------------------------------------------------------------
-- registry

M.specs = {}

local function spec(s) M.specs[#M.specs + 1] = s end

local function count_initial(states)
    local n = 0
    for _, s in ipairs(states) do if s.initial then n = n + 1 end end
    return n
end

spec{key = "nonempty", name = "at least one state", sev = "error",
run = function(M, _, out)
    if #(M.states or {}) == 0 then
        out[#out + 1] = {msg = "no states"}
    end
end}

spec{key = "one_initial", name = "one initial state",
     sev = "error",
run = function(M, _, out)
    local n = count_initial(M.states or {})
    if n == 0 and #(M.states or {}) > 0 then
        out[#out + 1] = {msg = "no initial state"}
    elseif n > 1 then
        for _, s in ipairs(M.states) do
            if s.initial then
                out[#out + 1] = {node = s.id,
                    msg = "extra initial state: " ..
                          tostring(s.name or s.id)}
            end
        end
    end
end}

spec{key = "unique_names", name = "names unique", sev = "error",
run = function(M, _, out)
    local seen = {}
    for _, s in ipairs(M.states or {}) do
        local nm = s.name or ""
        if seen[nm] then
            out[#out + 1] = {node = s.id,
                msg = "duplicate state name '" .. nm .. "'"}
        else
            seen[nm] = s.id
        end
    end
end}

spec{key = "endpoints", name = "endpoints exist",
     sev = "error",
run = function(M, _, out)
    local ids = {}
    for _, s in ipairs(M.states or {}) do ids[s.id] = true end
    for _, e in ipairs(M.transitions or {}) do
        if not ids[e.from] or not ids[e.to] then
            out[#out + 1] = {edge = e.id,
                msg = "dangling endpoint"}
        end
    end
end}

spec{key = "labels", name = "labels fit type",
     sev = "error",
run = function(M, _, out)
    local structured = label_lang and label_lang.is_structured(M.type)
    if not label_lang
       and ((M.type or ""):match("^d?pda")
            or (M.type or ""):match("^n?tm")) then
        out[#out + 1] = {msg = "label grammar module missing "
            .. "(automata.label_lang) — checks degraded"}
    end
    for _, e in ipairs(M.transitions or {}) do
        if structured then
            local t, why = label_lang.parse_many(M.type, e.label)
            if not t then
                out[#out + 1] = {edge = e.id, msg = why}
            end
        else
            local syms, eps = parse_label(e.label)
            if not syms then
                -- eps holds the reason when syms is nil
                out[#out + 1] = {edge = e.id, msg = eps}
            elseif eps and is_dfa(M.type) then
                out[#out + 1] = {edge = e.id,
                    msg = "epsilon on a DFA"}
            elseif eps and M.type == "nfa" then
                out[#out + 1] = {edge = e.id,
                    msg = "epsilon on an NFA"}
            end
        end
    end
end}

spec{key = "alphabet", name = "in alphabet",
     sev = "error",
run = function(M, _, out)
    local _, aset = parse_alphabet(M.alphabet)
    if not aset then return end     -- no alphabet configured: nothing
    local _, sset = parse_alphabet(M.stack_alphabet)
    local structured = label_lang and label_lang.is_structured(M.type)
    local function flag(e, s, what)
        out[#out + 1] = {edge = e.id,
            msg = "'" .. s .. "' not in " .. what}
    end
    for _, e in ipairs(M.transitions or {}) do            -- to check
        if structured then
            local ts = label_lang.parse_many(M.type, e.label)
            if ts and label_lang.is_pda(M.type) then
                for _, t in ipairs(ts) do
                    if t.input ~= "" and not aset[t.input] then
                        flag(e, t.input, "alphabet")
                    end
                    if sset then
                        if t.pop ~= "" and not sset[t.pop] then
                            flag(e, t.pop, "stack alphabet")
                        end
                        for i = 1, #t.push do
                            local c = t.push:sub(i, i)
                            if c ~= "λ" and c ~= " "
                               and not sset[c] then
                                flag(e, c, "stack alphabet")
                            end
                        end
                    end
                end
            elseif ts then
                -- tm/tm-N: reads and writes must be tape symbols
                for _, t in ipairs(ts) do
                    for _, c in ipairs(t) do
                        local r, w = c[1], c[2]
                        if r ~= "B" and not aset[r] then
                            flag(e, r, "alphabet")
                        end
                        if w and w ~= "B" and not aset[w] then
                            flag(e, w, "alphabet")
                        end
                    end
                end
            end
        else
            local syms = parse_label(e.label)
            if syms then
                local bad = {}
                for _, s in ipairs(syms) do
                    if not aset[s] and not bad[s] then
                        bad[s] = true
                        out[#out + 1] = {edge = e.id,
                            msg = "'" .. s .. "' not in alphabet"}
                    end
                end
            end
        end
    end
end}

spec{key = "deterministic", name = "deterministic",
     sev = "error", dfa_only = true,
run = function(M, _, out)
    if label_lang and label_lang.is_det_pda
       and label_lang.is_det_pda(M.type) then
        -- Sudkamp determinism (dpda types only — plain pda is
        -- nondeterministic): transitions from one state conflict
        -- when their inputs can apply together (equal or either λ)
        -- AND their pops can hold together (equal or either λ)
        local ts = {}
        for _, e in ipairs(M.transitions or {}) do
            for _, t in ipairs(
                    label_lang.parse_many(M.type, e.label) or {}) do
                ts[#ts + 1] = {from = e.from, id = e.id, t = t,
                               label = label_lang.pda_label(t)}
            end
        end
        for i = 1, #ts do
            for j = i + 1, #ts do
                local a, b = ts[i], ts[j]
                if a.from == b.from then
                    local ic = a.t.input == b.t.input
                               or a.t.input == "" or b.t.input == ""
                    local pc = a.t.pop == b.t.pop
                               or a.t.pop == "" or b.t.pop == ""
                    if ic and pc then
                        out[#out + 1] = {node = a.from, edge = a.id,
                            msg = "nondeterministic with '" ..
                                  b.label .. "'"}
                        out[#out + 1] = {node = a.from, edge = b.id,
                            msg = "nondeterministic with '" ..
                                  a.label .. "'"}
                    end
                end
            end
        end
        return
    end
    if label_lang and label_lang.is_det_tm
       and label_lang.is_det_tm(M.type) then
        -- TM (deterministic variants only — ntm* branches freely):
        -- two transitions from one state with the same read
        -- tuple (on every tape) compete
        local per = {}
        for _, e in ipairs(M.transitions or {}) do
            for _, t in ipairs(
                    label_lang.parse_many(M.type, e.label) or {}) do
                local reads = {}
                for _, c in ipairs(t) do reads[#reads + 1] = c[1] end
                local key = table.concat(reads, "|")
                local m = per[e.from]
                if not m then m = {}; per[e.from] = m end
                local g = m[key]
                if not g then g = {}; m[key] = g end
                g[#g + 1] = e.id
            end
        end
        for from, m in pairs(per) do
            for key, g in pairs(m) do
                if #g > 1 then
                    for _, id in ipairs(g) do
                        out[#out + 1] = {node = from, edge = id,
                            msg = #g .. " transitions read '" ..
                                  key .. "'"}
                    end
                end
            end
        end
        return
    end
    if not is_dfa(M.type) then return end
    local per = {}      -- state id -> symbol -> {transition ids}
    for _, e in ipairs(M.transitions or {}) do
        local syms, eps = parse_label(e.label)
        if syms and eps then          -- eps is the reason string when
            out[#out + 1] = {node = e.from, edge = e.id,   -- syms=nil
                msg = "nondeterministic: epsilon"}
        end
        for _, s in ipairs(syms or {}) do
            local m = per[e.from]
            if not m then m = {}; per[e.from] = m end
            local g = m[s]
            if not g then g = {}; m[s] = g end
            g[#g + 1] = e.id
        end
    end
    -- every member of a conflicting (state, symbol) group is flagged:
    -- removing any n-1 of them fixes it, so none is "the good one"
    for from, m in pairs(per) do
        for s, g in pairs(m) do
            if #g > 1 then
                for _, id in ipairs(g) do
                    out[#out + 1] = {node = from, edge = id,
                        msg = #g .. " '" .. s ..
                              "' transitions"}
                end
            end
        end
    end
end}

spec{key = "total", name = "total (DFA)",
     sev = "error", dfa_only = true, needs_alphabet = true,
run = function(M, _, out)
    if M.type ~= "dfa" then return end   -- "dfa-part" is the explicit
                                         -- incomplete variant
    local alist, aset = parse_alphabet(M.alphabet)
    if not aset then
        -- no alphabet configured: infer it as the union of all
        -- symbols occurring on transitions — a total DFA must offer
        -- every symbol that occurs anywhere at every state.  With no
        -- symbols at all nothing can be checked.
        alist, aset = {}, {}
        for _, e in ipairs(M.transitions or {}) do
            for _, s in ipairs(parse_label(e.label) or {}) do
                if not aset[s] then
                    aset[s] = true
                    alist[#alist + 1] = s
                end
            end
        end
        if #alist == 0 then
            if #(M.states or {}) > 0 then
                out[#out + 1] = {sev = "warning",
                                 msg = "no alphabet; " ..
                                       "total unchecked"}
            end
            return
        end
    end
    local cover = {}    -- state id -> set
    for _, e in ipairs(M.transitions or {}) do
        local syms = parse_label(e.label)
        local m = cover[e.from]
        if not m then m = {}; cover[e.from] = m end
        for _, s in ipairs(syms or {}) do m[s] = true end
    end
    local name = {}
    for _, s in ipairs(M.states or {}) do name[s.id] = s.name end
    for _, s in ipairs(M.states or {}) do
        local missing = {}
        for _, a in ipairs(alist) do
            local m = cover[s.id]
            if not (m and m[a]) then missing[#missing + 1] = a end
        end
        if #missing > 0 then
            out[#out + 1] = {node = s.id,
                msg = "q=" .. tostring(name[s.id] or s.id) ..
                      " misses " ..
                      table.concat(missing, ", ")}
        end
    end
end}

spec{key = "reachable", name = "all reachable", sev = "warning",
run = function(M, _, out)
    local states = M.states or {}
    local adj, seen, start = {}, {}, nil
    for _, s in ipairs(states) do
        if s.initial and not start then start = s.id end
    end
    if not start then return end
    for _, e in ipairs(M.transitions or {}) do
        local m = adj[e.from]
        if not m then m = {}; adj[e.from] = m end
        m[#m + 1] = e.to
    end
    local queue = {start}
    seen[start] = true
    while #queue > 0 do
        local u = table.remove(queue, 1)
        for _, v in ipairs(adj[u] or {}) do
            if not seen[v] then seen[v] = true; queue[#queue + 1] = v end
        end
    end
    for _, s in ipairs(states) do
        if not seen[s.id] then
            out[#out + 1] = {node = s.id,
                msg = tostring(s.name or s.id) ..
                      " unreachable"}
        end
    end
end}

spec{key = "has_accepting", name = "has accepting",
     sev = "warning",
run = function(M, _, out)
    -- empty-stack acceptance makes F superfluous: the lecture's
    -- L_E(M) ignores the state at the end of the computation
    if label_lang and label_lang.pda_accept
       and label_lang.pda_accept(M.type) == "e" then return end
    for _, s in ipairs(M.states or {}) do
        if s.accepting then return end
    end
    if #(M.states or {}) > 0 then
        out[#out + 1] = {msg = "no accepting state"}
    end
end}

spec{key = "no_duplicates", name = "no duplicates",
     sev = "warning",
run = function(M, _, out)
    local groups, order = {}, {}
    for _, e in ipairs(M.transitions or {}) do
        local k = tostring(e.from) .. ">" .. tostring(e.to) ..
                  ">" .. tostring(e.label)
        local g = groups[k]
        if not g then g = {}; groups[k] = g; order[#order + 1] = k end
        g[#g + 1] = e.id
    end
    -- like the determinism check, all copies are marked: deleting any
    -- one of them resolves the group
    for _, k in ipairs(order) do
        local g = groups[k]
        if #g > 1 then
            for _, id in ipairs(g) do
                out[#out + 1] = {edge = id,
                    msg = "duplicate transition"}
            end
        end
    end
end}

-- ---------------------------------------------------------------
-- regular-expression checks: only relevant while the model is in
-- "re" mode — the modes filter below keeps them out of automaton
-- work (and keeps "no states" out of expression work)

-- client side loads this module as server.checks, the spawned server
-- as plain checks — try both names
local ok_re, regex = pcall(require, "server.regex")
if not ok_re then regex = require "regex" end

spec{key = "re_syntax", name = "expression parses",
     sev = "error", modes = {re = true},
run = function(M, _, out)
    -- an empty field is a missing input, not a malformed one — the
    -- exercise decides whether the answer may be left out
    if not M.regex or M.regex:match("^%s*$") then return end
    local ast, err = regex.parse(M.regex)
    if not ast then
        out[#out + 1] = {msg = err.msg .. " @" .. err.pos,
                         re_pos = err.pos}
    end
end}

spec{key = "re_alphabet", name = "in alphabet",
     sev = "error", modes = {re = true},
run = function(M, _, out)
    local _, aset = parse_alphabet(M.alphabet)
    if not aset then return end
    local ast = regex.parse(M.regex)
    if not ast then return end
    for s in pairs(regex.symbols(ast)) do
        if not aset[s] then
            out[#out + 1] = {msg = "'" .. s .. "' not in alphabet"}
        end
    end
end}

-- ---------------------------------------------------------------
-- driver

-- the client's default toggle state: every check on
function M.defaults()
    local d = {}
    for _, s in ipairs(M.specs) do d[s.key] = (s.default ~= false) end
    return d
end

-- run every ENABLED check; `enabled` maps key -> bool (missing key =
-- the spec's default).  Returns the flat problem list.
function M.run(model, enabled)
    model = model or {}
    -- back-compat: the older wire shape carried {type="dfa",
    -- partial=true} — the type string now encodes it
    if model.type == "dfa" and model.partial then
        model.type = "dfa-part"
    end
    model.states = model.states or {}
    model.transitions = model.transitions or {}
    enabled = enabled or {}
    -- the task mode scopes which object is under test: automaton
    -- specs (the default, no modes list) run only in "aut" mode,
    -- a spec naming modes runs only for those — "no states" must
    -- not fire while the student edits a regular expression
    local mode = model.mode or "aut"
    local problems = {}
    for _, s in ipairs(M.specs) do
        local on = enabled[s.key]
        if on == nil then on = (s.default ~= false) end
        local in_mode = s.modes and s.modes[mode]
                        or (not s.modes and mode == "aut")
        if on and in_mode then
            local out = {}
            s.run(model, nil, out)
            for _, p in ipairs(out) do
                p.sev = p.sev or s.sev   -- a check may override the
                p.key = s.key            -- spec default per problem
                problems[#problems + 1] = p
            end
        end
    end
    return problems
end

return M
