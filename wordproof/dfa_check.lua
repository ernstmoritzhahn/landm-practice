-- wordproof/dfa_check.lua — grading for exercise 1.3 (DFA tasks):
-- the automata-ime editor answers with a JSON model
--   {type="dfa"|"nfa"|..., alphabet="a,b",
--    states=[{id,name,initial,accepting}],
--    transitions=[{id,from,to,label}]}
-- which is turned into an automata DFA here, validated structurally and
-- compared against the task's reference DFA via compare_dfa.
-- Also: per-word run ("trace") checking, acceptance checking and
-- transition-table checking for the composite J/K tasks.

local json = require "lib.json"
require("lib.util").fix_path()
local automata = require "automata"
local RC = require "wordproof.regexp_check"

local M = {}

-- ---------------- reference DFAs ----------------
local ref_cache = {}
local function ref_dfa(str)
    if ref_cache[str] then return ref_cache[str] end
    local dfa = automata.parse_dfa(str)
    ref_cache[str] = dfa
    return dfa
end

-- "a,b" / "ab" / "a b" -> list + set (same rules as the editor's checks)
local function parse_alphabet(str)
    str = (str or ""):gsub("^%s+", ""):gsub("%s+$", "")
    if str == "" then return nil end
    local list, set = {}, {}
    if str:find(",") or str:find("%s") then
        for tok in str:gmatch("[^,%s]+") do
            if tok ~= "" and not set[tok] then
                set[tok] = true; list[#list + 1] = tok
            end
        end
    else
        for i = 1, #str do
            local c = str:sub(i, i)
            if not set[c] then set[c] = true; list[#list + 1] = c end
        end
    end
    return list, set
end

-- transition label "a,b" -> {"a","b"} ; empty label is malformed on DFA
local function parse_label(label)
    label = label or ""
    if label:match("^%s*$") then return nil, "empty label" end
    local syms = {}
    for part in (label .. ","):gmatch("(.-),") do
        local t = part:gsub("^%s+", ""):gsub("%s+$", "")
        if t == "" then
            return nil, "empty symbol in label"
        end
        syms[#syms + 1] = t
    end
    return syms
end

-- nondeterministic types: "nfa" rejects lambda steps, "nfa-eps"
-- (a.k.a. "nfa-lambda") accepts the explicit λ label
local function is_nfa_type(t)
    return t == "nfa" or t == "nfa-eps" or t == "nfa-lambda"
end
local function eps_type(t)
    return t == "nfa-eps" or t == "nfa-lambda"
end

-- decoded editor model -> dfa, problems, missing | nil, problems
local function model_to_dfa(m, expect_type, partial_ok)
    local problems = {}
    if type(m) ~= "table" or not m.states or #m.states == 0 then
        return nil, {"no automaton drawn yet"}
    end
    local dfa = automata.make_dfa()
    -- alphabet: the task's alphabet wins; the model's own only as backup
    local alpha_list, alpha_set = parse_alphabet(m.alphabet)
    if alpha_list then
        for _,s in ipairs(alpha_list) do dfa:add_symbol(s) end
    end
    -- states
    local names, by_name, initial = {}, {}, nil
    for _, s in ipairs(m.states) do
        local nm = tostring(s.name or s.id)
        if by_name[nm] then
            problems[#problems + 1] = "duplicate state name '" .. nm .. "'"
        else
            by_name[nm] = s
            names[#names + 1] = nm
            dfa:add_state(nm)
            if s.initial then
                if initial then
                    problems[#problems + 1] = "more than one initial state"
                else
                    initial = nm
                    dfa:set_initial(nm, true)
                end
            end
            if s.accepting then dfa:set_accepting(nm, true) end
        end
    end
    if not initial then problems[#problems + 1] = "no initial state" end
    -- overlapping states hide each other on the canvas (grid snap can
    -- stack them exactly); the resulting "missing transition from q3"
    -- complaints read as nonsense, so flag the overlap explicitly first
    for i = 1, #m.states - 1 do
        for j = i + 1, #m.states do
            local a, b = m.states[i], m.states[j]
            if type(a.x) == "number" and type(a.y) == "number"
                    and type(b.x) == "number" and type(b.y) == "number" then
                local dx = a.x - b.x
                local dy = a.y - b.y
                if dx * dx + dy * dy < 35 * 35 then
                    problems[#problems + 1] = "states "
                        .. tostring(a.name or a.id) .. " and "
                        .. tostring(b.name or b.id)
                        .. " overlap — drag them apart"
                end
            end
        end
    end
    -- transitions: model ids are editor ids, resolve to names first
    local name_of = {}
    for _, s in ipairs(m.states) do
        name_of[s.id] = s.name or tostring(s.id)
        name_of[s.name] = name_of[s.id]
    end
    local seen = {}
    for _, e in ipairs(m.transitions or {}) do
        local from, to = name_of[e.from], name_of[e.to]
        if not (from and to) then
            problems[#problems + 1] = "transition with unknown endpoint"
        else
            local syms, perr = parse_label(e.label)
            if not syms then
                problems[#problems + 1] = "transition " .. from .. "→"
                    .. to .. ": " .. perr
            else
                for _, sym in ipairs(syms) do
                    if sym == "λ" then
                        problems[#problems + 1] = "epsilon (λ) transition "
                            .. "on a DFA"
                    elseif alpha_set and not alpha_set[sym] then
                        problems[#problems + 1] = "'" .. sym
                            .. "' is not in the alphabet"
                    else
                        if not alpha_set then dfa:add_symbol(sym) end
                        local key = from .. "\0" .. sym
                        if not is_nfa_type(expect_type) and seen[key] then
                            problems[#problems + 1] = "nondeterministic: "
                                .. "two " .. sym .. "-transitions leave "
                                .. from
                        elseif not seen[key] then
                            dfa:add_transition(from, sym, to)
                            seen[key] = true
                        end
                    end
                end
            end
        end
    end
    -- totality (DFA only): every model DFA on the sheets is total
    -- and an incomplete one loses exam points, so missing
    -- transitions are problems by default.  Tasks that follow the
    -- worksheets' rare partial-machine convention set partial_ok;
    -- then the gaps come back as notes instead and the language
    -- check judges the machine as drawn (missing = reject).
    local missing = {}
    if not is_nfa_type(expect_type) then
        local syms = {}
        for s, _ in pairs(dfa:get_symbols() or {}) do
            syms[#syms + 1] = s
        end
        for _, nm in ipairs(names) do
            for _, sym in ipairs(syms) do
                if not seen[nm .. "\0" .. sym] then
                    if partial_ok then
                        missing[#missing + 1] = nm .. "(" .. sym .. ")"
                    else
                        problems[#problems + 1] = "missing " .. sym
                            .. "-transition from " .. nm
                    end
                end
            end
        end
    end
    return dfa, problems, missing
end

-- decoded editor model -> nfa/nfa-lambda, problems | nil, problems
-- Same structure as model_to_dfa but parallel transitions are legal
-- (the NFA stores target SETS per (from,label)), λ labels become
-- epsilon transitions for eps types, and there is no totality check.
local function model_to_nfa(m, expect_type)
    local problems = {}
    if type(m) ~= "table" or not m.states or #m.states == 0 then
        return nil, {"no automaton drawn yet"}
    end
    local nfa = automata.make_nfa(eps_type(expect_type))
    local alpha_list, alpha_set = parse_alphabet(m.alphabet)
    if alpha_list then
        for _,s in ipairs(alpha_list) do nfa:add_symbol(s) end
    end
    local names, by_name, initial = {}, {}, nil
    for _, s in ipairs(m.states) do
        local nm = tostring(s.name or s.id)
        if by_name[nm] then
            problems[#problems + 1] = "duplicate state name '" .. nm .. "'"
        else
            by_name[nm] = s
            names[#names + 1] = nm
            nfa:add_state(nm)
            if s.initial then
                if initial then
                    problems[#problems + 1] = "more than one initial state"
                else
                    initial = nm
                    nfa:set_initial(nm, true)
                end
            end
            if s.accepting then nfa:set_accepting(nm, true) end
        end
    end
    if not initial then problems[#problems + 1] = "no initial state" end
    for i = 1, #m.states - 1 do
        for j = i + 1, #m.states do
            local a, b = m.states[i], m.states[j]
            if type(a.x) == "number" and type(a.y) == "number"
                    and type(b.x) == "number" and type(b.y) == "number" then
                local dx = a.x - b.x
                local dy = a.y - b.y
                if dx * dx + dy * dy < 35 * 35 then
                    problems[#problems + 1] = "states "
                        .. tostring(a.name or a.id) .. " and "
                        .. tostring(b.name or b.id)
                        .. " overlap — drag them apart"
                end
            end
        end
    end
    local name_of = {}
    for _, s in ipairs(m.states) do
        name_of[s.id] = s.name or tostring(s.id)
        name_of[s.name] = name_of[s.id]
    end
    for _, e in ipairs(m.transitions or {}) do
        local from, to = name_of[e.from], name_of[e.to]
        if not (from and to) then
            problems[#problems + 1] = "transition with unknown endpoint"
        else
            local syms, perr = parse_label(e.label)
            if not syms then
                problems[#problems + 1] = "transition " .. from .. "→"
                    .. to .. ": " .. perr
            else
                for _, sym in ipairs(syms) do
                    if sym == "λ" then
                        if eps_type(expect_type) then
                            nfa:add_transition(from, "λ", to)
                        else
                            problems[#problems + 1] = "epsilon (λ) "
                                .. "transition on an NFA"
                        end
                    elseif alpha_set and not alpha_set[sym] then
                        problems[#problems + 1] = "'" .. sym
                            .. "' is not in the alphabet"
                    else
                        if not alpha_set then nfa:add_symbol(sym) end
                        nfa:add_transition(from, sym, to)
                    end
                end
            end
        end
    end
    return nfa, problems
end

-- reference for aut parts: an automaton tuple ("({q0,...},...)") is
-- parsed as an NFA-λ (DFA tuples are just deterministic NFAs); anything
-- else is a regular expression converted by the Thompson construction.
-- Returns (automaton, is_tuple) — the flag gates the state-count
-- warning, which is meaningless against a generated Thompson machine.
-- Separate cache: ref_dfa stores bare automata under the same keys.
local ref_any_cache = {}
local function ref_any(reference)
    -- a reference may be a string (regexp or tuple) or a precomputed
    -- automaton — either the object itself or a 0-ary function
    -- returning it (lazy: built on first check)
    if type(reference) == "function" then
        local hit = ref_any_cache[reference]
        if hit then return hit.aut, hit.tuple end
        local aut = reference()
        ref_any_cache[reference] = { aut = aut, tuple = false }
        return aut, false
    end
    if type(reference) == "table" and reference.get_states then
        return reference, false
    end
    local hit = ref_any_cache[reference]
    if hit then return hit.aut, hit.tuple end
    local aut, is_tuple
    if (reference or ""):match("^%s*%({") then
        aut = automata.parse_nfa_lambda(reference)
        is_tuple = true
    else
        aut = automata.regexp_to_nfa_lambda(
            automata.parse_regexp_string(reference))
    end
    ref_any_cache[reference] = { aut = aut, tuple = is_tuple }
    return aut, is_tuple
end

-- the complement machine: determinise (NFAs included), complete, then
-- flip acceptance — only on a TOTAL dfa is flipping sound
local function complemented(ref)
    local d = ref
    if not automata.is_finished_dfa(d) then
        d = automata.nfa_to_dfa(d)
    end
    d = automata.complete_dfa(d)
    for s, _ in pairs(d:get_states()) do
        d:set_accepting(s, not d:is_accepting(s))
    end
    return d
end

-- ---------------- the DFA run ----------------
local function run_states(dfa, word)
    local seq = { dfa:get_initial() }
    local cur = dfa:get_initial()
    for i = 1, #word do
        cur = dfa:get_to_states(cur, word:sub(i, i))
        if not cur then return seq, false end   -- stuck (partial dfa)
        seq[#seq + 1] = cur
    end
    return seq, true
end

-- split "q0 q0 q1" | "q0,q0,q1" | "q0→q0→q1" | "q0q0q1q2" (single-char
-- names only for the bare form — split on state-name prefix match)
local function split_seq(s, known)
    s = (s or ""):gsub("[λε]", "")
    local parts = {}
    for tok in s:gmatch("[%w_]+") do parts[#parts + 1] = tok end
    -- the bare form "q0q0q1" tokenises as one word; try to split it by
    -- prefix-matching known state names (longest first)
    if #parts == 1 and known then
        local one = parts[1]
        local sorted = {}
        for nm,_ in pairs(known) do sorted[#sorted + 1] = nm end
        table.sort(sorted, function(a,b) return #a > #b end)
        local split, i, ok = {}, 1, true
        while i <= #one do
            local hit
            for _, nm in ipairs(sorted) do
                if one:sub(i, i + #nm - 1) == nm then hit = nm; break end
            end
            if not hit then ok = false; break end
            split[#split + 1] = hit
            i = i + #hit
        end
        if ok then parts = split end
    end
    return parts
end

-- ---------------- per-part graders ----------------

local function word_or_lam(w)
    if w == nil then return nil end
    return w == "" and "λ" or w
end

-- ---------------------------------------------------------------------
-- structural isomorphism for part.structure parts: language equality
-- alone cannot see a misdrawn construction (a wrong automaton may
-- still accept the same language).  The reachable part of the student
-- automaton must be isomorphic to the reference construction — same
-- states (up to names), same transition multiset, same initial state,
-- same accepting set.  Extra UNREACHABLE states (e.g. a pair state
-- drawn for completeness) do not fail the check: the sheet itself
-- only draws the reachable product.
local function norm_label(l)
    if l == "" or l == "λ" or l == "eps" or l == "lambda" or l == "lamda" then
        return "λ"
    end
    return tostring(l)
end

-- states reachable from the initial state (any label incl. λ) plus
-- the transitions inside that set
local function reachable_part(aut)
    local reach, stack = {}, {}
    local init = aut:get_initial()
    if init then reach[init] = true; stack[1] = init end
    local all = aut:get_transitions()
    while #stack > 0 do
        local s = table.remove(stack)
        for _, t in ipairs(all) do
            if t.from == s and not reach[t.target] then
                reach[t.target] = true
                stack[#stack + 1] = t.target
            end
        end
    end
    local ts = {}
    for _, t in ipairs(all) do
        if reach[t.from] and reach[t.target] then
            ts[#ts + 1] = t
        end
    end
    return reach, ts
end

-- signature per state: accepting flag + in/out label multisets +
-- self-loop labels — a bijection must map signatures 1:1
local function state_sig(aut, s, out, into)
    local acc = aut:is_accepting(s) and "F" or "."
    local parts = {acc}
    for l, m in pairs(out[s] or {}) do
        local n = 0
        for _, c in pairs(m) do n = n + c end
        parts[#parts+1] = ">"..l..":"..n
    end
    for l, m in pairs(into[s] or {}) do
        local n = 0
        for _, c in pairs(m) do n = n + c end
        parts[#parts+1] = "<"..l..":"..n
    end
    table.sort(parts)
    return table.concat(parts, ",")
end

local function aut_isomorphic(a, b)
    local ra, ta = reachable_part(a)
    local rb, tb = reachable_part(b)
    local na, nb = 0, 0
    for _ in pairs(ra) do na = na + 1 end
    for _ in pairs(rb) do nb = nb + 1 end
    if na ~= nb then
        return false, "reachable part has " .. na .. " states, "
                   .. "the construction gives " .. nb
    end
    if #ta ~= #tb then
        return false, "reachable part has " .. #ta .. " transitions, "
                   .. "the construction gives " .. #tb
    end
    -- adjacency: out[s][l][t] = n, into[t][l][s] = n
    local function adj(ts)
        local out, into = {}, {}
        for _, t in ipairs(ts) do
            local l = norm_label(t.label)
            local o = out[t.from] or {}; out[t.from] = o
            local m = o[l] or {}; o[l] = m
            m[t.target] = (m[t.target] or 0) + 1
            local i2 = into[t.target] or {}; into[t.target] = i2
            local m2 = i2[l] or {}; i2[l] = m2
            m2[t.from] = (m2[t.from] or 0) + 1
        end
        return out, into
    end
    local aout, ainto = adj(ta)
    local bout, binto = adj(tb)
    -- order a-states by rarest signature (fail fast)
    local bsigs, bcount = {}, {}
    for s in pairs(rb) do
        local g = state_sig(b, s, bout, binto)
        bsigs[s] = g
        bcount[g] = (bcount[g] or 0) + 1
    end
    local alist = {}
    for s in pairs(ra) do
        local g = state_sig(a, s, aout, ainto)
        if not bcount[g] then
            return false, "no state matches " .. tostring(s)
                       .. "'s neighbourhood (labels/accepting)"
        end
        alist[#alist+1] = {s = s, sig = g, rare = bcount[g]}
    end
    table.sort(alist, function(x, y) return x.rare < y.rare end)
    -- backtracking with forward checking on already-mapped neighbours
    local map, used_b = {}, {}
    local init_a, init_b = a:get_initial(), b:get_initial()
    local function edge_need(out, s, l, t)
        local o = out[s] and out[s][l]; return o and o[t] or 0
    end
    local function dfs(k)
        if k > #alist then return true end
        local s, sg = alist[k].s, alist[k].sig
        for u in pairs(rb) do
            if not used_b[u] and bsigs[u] == sg
               and a:is_accepting(s) == b:is_accepting(u)
               and (s == init_a) == (u == init_b) then
                local okm = true
                -- self-loops at s must exist at u (s not yet in map,
                -- so the neighbour scan below cannot see them)
                for l, m in pairs(aout[s] or {}) do
                    if (m[s] or 0) > edge_need(bout, u, l, u) then
                        okm = false break
                    end
                end
                -- every transition between s and an already-mapped
                -- state must exist between u and its image, with
                -- multiplicity, in both directions (s as source,
                -- s as target, s->s loops land in both checks)
                for v, mv in pairs(map) do
                    for l, m in pairs(aout[s] or {}) do
                        local need = m[v] or 0
                        if need > edge_need(bout, u, l, mv) then
                            okm = false break
                        end
                    end
                    for l, m in pairs(ainto[s] or {}) do
                        local need = m[v] or 0
                        if need > edge_need(binto, u, l, mv) then
                            okm = false break
                        end
                    end
                    if not okm then break end
                end
                if okm then
                    map[s], used_b[u] = u, true
                    if dfs(k + 1) then return true end
                    map[s], used_b[u] = nil, nil
                end
            end
        end
        return false
    end
    if dfs(1) then return true end
    return false, "the reachable structure differs from the "
               .. "construction (check state pairs and transitions)"
end

-- part.kind == "aut": structural problems + language equivalence
function M.check_aut(part, model_json, expect_type)
    local ok, m = pcall(json.decode, model_json or "")
    if not ok or type(m) ~= "table" then
        return { ok=false, kind="empty",
                 msg="no automaton — draw the state diagram" }
    end
    if m.type == "re" or (m.states and #m.states == 0) then
        return { ok=false, kind="empty",
                 msg="no automaton — draw the state diagram" }
    end
    -- graphical PDA / Turing-machine input delegates to the dedicated
    -- checkers; their labels parse through automata.label_lang
    if part.aut_type == "pda" then
        return require("wordproof.pda_check")
            .check_pda_model(part, model_json)
    end
    if part.aut_type == "tm"
       or (part.aut_type or ""):match("^tm%-%d+$") then
        return require("wordproof.tm_check")
            .check_tm_model(part, model_json)
    end
    local aut, problems, missing
    if is_nfa_type(part.aut_type) then
        aut, problems = model_to_nfa(m, part.aut_type)
    else
        aut, problems, missing =
            model_to_dfa(m, part.aut_type, part.partial_ok)
    end
    if not aut then
        return { ok=false, kind="fail", msg=table.concat(problems,"; ") }
    end
    if #problems > 0 then
        return { ok=false, kind="fail",
                 msg=table.concat(problems, ";  ") }
    end
    -- a partial diagram is a hint, not a failure — the language
    -- semantics (missing transition = reject) is checked normally
    local note
    if missing and #missing > 0 then
        local bits = {}
        for i = 1, math.min(3, #missing) do
            bits[#bits + 1] = missing[i]
        end
        note = "the diagram is not total — no transition for "
            .. table.concat(bits, ", ")
            .. (#missing > 3 and ", …" or "")
            .. "; a missing transition rejects, so a complete DFA "
            .. "would route them to a non-accepting sink"
    end
    local ref, is_tuple = ref_any(part.reference)
    if part.complement then ref = complemented(ref) end
    local cmp, cex_s, cex_r = automata.compare_languages(aut, ref)
    if cmp ~= "=" then
        local parts = {}
        if cex_s then parts[#parts+1] = "'" .. word_or_lam(cex_s)
            .. "' is accepted but not in L" end
        if cex_r then parts[#parts+1] = "'" .. word_or_lam(cex_r)
            .. "' is in L but not accepted" end
        return { ok=false, kind="mismatch",
                 msg=table.concat(parts, ";  ")
                    .. (note and "  (" .. note .. ")" or "") }
    end
    if part.structure then
        -- the exercise grades a CONSTRUCTION (projection, product):
        -- the reachable part must be the construction result itself,
        -- not just any automaton for the right language
        local iso, why = aut_isomorphic(aut, ref)
        if not iso then
            return { ok=false, kind="mismatch",
                     msg="accepts the right language, but the "
                      .. "structure is not the construction: " .. why }
        end
        return { ok=true, msg=note }
    end
    if not is_tuple or is_nfa_type(part.aut_type) then
        return { ok=true, msg=note }
    end
    local n_student, want = 0, part.exact_states
    for _ in pairs(aut:get_states()) do n_student = n_student + 1 end
    if not want then
        want = 0
        for _ in pairs(ref:get_states()) do want = want + 1 end
        if n_student ~= want then
            -- no exact-size requirement: a correct-language automaton
            -- IS a correct answer — the size difference is a note,
            -- not an error (the reference is unnamed; say "a DFA",
            -- not "M" — no M was introduced in the task)
            local msg
            if n_student > want then
                msg = "accepts the right language — correct; a DFA "
                   .. "with " .. want .. " states exists (yours has "
                   .. n_student .. ")"
            else
                msg = "accepts the right language — correct; even "
                   .. "smaller than the reference (yours has "
                   .. n_student .. " states, it has " .. want .. ")"
            end
            if note then msg = msg .. ";  " .. note end
            return { ok=true, kind="warn", msg=msg }
        end
    elseif n_student ~= want then
        return { ok=false, kind="warn",
                 msg="accepts the right language, but it must have "
                  .. "exactly " .. want .. " states — yours has "
                  .. n_student
                  .. (note and ";  " .. note or "") }
    end
    return { ok=true, msg=note }
end

-- part.check == "compose" (guided construction): the student wires
-- given component automata together.  part.seeds_locked lists the stage
-- labels; pd.seeds[stage] carries the LIVE effective automaton of that
-- stage as JSON (the stage's simplify output when present, else its
-- compose output).  The embedded copy inside the result is identified
-- by seed tags / the "<stage>_" name prefix.  Checks, in order:
--   1. freshness — embedded component still equals the live stage
--      automaton (else: "refresh components")
--   2. containment — every embedded state/transition present verbatim
--      (locked in the editor; catches hand-edited JSON)
--   3. integration — every embedded state reachable from the initial
--      state AND able to reach an accepting state (parking the given
--      component in a corner fails)
--   4. language equivalence, as for plain aut parts
local function name_index(m)
    local by_name = {}
    for _, s in ipairs(m.states or {}) do
        by_name[tostring(s.name or s.id)] = s
    end
    return by_name
end

-- label multiset per (from,to) name pair, lambda included
local function edge_sets(m)
    local id_name = {}
    for _, s in ipairs(m.states or {}) do
        id_name[tostring(s.id)] = tostring(s.name or s.id)
    end
    local sets = {}
    for _, e in ipairs(m.transitions or {}) do
        local f, t = id_name[tostring(e.from)], id_name[tostring(e.to)]
        if f and t then
            local key = f .. "\1" .. t
            local s = sets[key]
            if not s then s = {}; sets[key] = s end
            local lbl = tostring(e.label or "")
            if lbl == "" then lbl = "λ" end
            s[lbl] = (s[lbl] or 0) + 1
        end
    end
    return sets
end

-- the lecture's "composable" normal form: exactly one initial state
-- with in-degree 0 and exactly one final state with out-degree 0;
-- returns a short problem description or nil when the form holds
local function composable_problems(m)
    local id_name, adj, radj = {}, {}, {}
    for _, s in ipairs(m.states or {}) do
        id_name[tostring(s.id)] = tostring(s.name or s.id)
    end
    local n_init, n_fin, init, fin = 0, 0, nil, nil
    for _, s in ipairs(m.states or {}) do
        local nm = tostring(s.name or s.id)
        adj[nm], radj[nm] = {}, {}
        if s.initial then n_init = n_init + 1; init = nm end
        if s.accepting then n_fin = n_fin + 1; fin = nm end
    end
    for _, e in ipairs(m.transitions or {}) do
        local f = id_name[tostring(e.from)]
        local t = id_name[tostring(e.to)]
        if f and t then adj[f][t] = true; radj[t][f] = true end
    end
    if n_init ~= 1 then
        return "exactly one initial state expected (found "
            .. n_init .. ")"
    end
    if next(radj[init] or {}) then
        return "the initial state must have no incoming transitions"
    end
    if n_fin ~= 1 then
        return "exactly one final state expected (found "
            .. n_fin .. ")"
    end
    if next(adj[fin] or {}) then
        return "the final state must have no outgoing transitions"
    end
    return nil
end

function M.check_compose(part, model_json, seeds)
    local ok, m = pcall(json.decode, model_json or "")
    if not ok or type(m) ~= "table"
       or not m.states or #m.states == 0 then
        return { ok=false, kind="empty",
                 msg="no automaton — draw the state diagram" }
    end
    local res_edges = edge_sets(m)
    -- embedded[tag] collects the states of one embedded component;
    -- entry "b#2" is a second copy of stage "b" (tag != stage).
    -- seed tags are authoritative; the name prefix is the fallback for
    -- models that lost their tags (without it tag "b" would wrongly
    -- swallow "b#2"'s "b_2_*" states through the "b_" prefix)
    local embedded = {}
    for _, tag in ipairs(part.seeds_locked or {}) do
        local prefix = tag:gsub("#", "_") .. "_"
        for _, s in ipairs(m.states) do
            if s.seed == tag then
                local e = embedded[tag]
                if not e then e = {}; embedded[tag] = e end
                e[#e + 1] = tostring(s.name or s.id)
            end
        end
        if not embedded[tag] then
            for _, s in ipairs(m.states) do
                local nm = tostring(s.name or s.id)
                if nm:sub(1, #prefix) == prefix then
                    local e = embedded[tag]
                    if not e then e = {}; embedded[tag] = e end
                    e[#e + 1] = nm
                end
            end
        end
    end
    -- adjacency over the whole submission, needed for the wiring,
    -- boundary and composable-form checks below
    local id_name, adj, radj = {}, {}, {}
    for _, s in ipairs(m.states) do
        id_name[tostring(s.id)] = tostring(s.name or s.id)
    end
    for _, s in ipairs(m.states) do
        adj[tostring(s.name or s.id)] = {}
        radj[tostring(s.name or s.id)] = {}
    end
    for _, e in ipairs(m.transitions or {}) do
        local f, t = id_name[tostring(e.from)],
                     id_name[tostring(e.to)]
        if f and t then
            adj[f][t] = true
            radj[t][f] = true
        end
    end
    for _, tag in ipairs(part.seeds_locked or {}) do
        local stage = tag:match("^[^#]+") or tag
        local prefix = tag:gsub("#", "_") .. "_"
        local shown = stage .. (tag ~= stage and " #" .. tag:sub(#stage + 2) or "")
        local seed_json = seeds and seeds[stage]
        local ok2, sm = pcall(json.decode, seed_json or "")
        if not (ok2 and type(sm) == "table"
                and sm.states and #sm.states > 0) then
            return { ok=false, kind="empty",
                     msg="component " .. shown .. ") is still empty "
                      .. "— finish that step first" }
        end
        -- a stage is a usable component only in composable form
        local cp = composable_problems(sm)
        if cp then
            return { ok=false, kind="composable",
                     msg="component " .. shown .. ") is not composable"
                      .. " — " .. cp .. " — fix that step first" }
        end
        local emb = embedded[tag]
        if not emb or #emb == 0 then
            return { ok=false, kind="comp_missing",
                     msg="the automaton for " .. shown .. ") is not "
                      .. "embedded — click 'refresh components'" }
        end
        -- freshness + containment: prefixed seed names and seed edges
        -- must appear verbatim in the result
        local emb_set = {}
        for _, nm in ipairs(emb) do emb_set[nm] = true end
        local seed_edges = edge_sets(sm)
        for _, s in ipairs(sm.states) do
            local want = prefix .. tostring(s.name or s.id)
            if not emb_set[want] then
                return { ok=false, kind="stale",
                         msg="component " .. shown .. ") changed since "
                          .. "it was embedded — click "
                          .. "'refresh components'" }
            end
        end
        for key, lbls in pairs(seed_edges) do
            local f, t = key:match("^(.-)\1(.*)$")
            local rk = prefix .. f .. "\1" .. prefix .. t
            local rs = res_edges[rk] or {}
            for lbl, cnt in pairs(lbls) do
                if (rs[lbl] or 0) < cnt then
                    return { ok=false, kind="comp_missing",
                             msg="component " .. shown .. ") was "
                              .. "altered — its states and transitions "
                              .. "must stay as given" }
                end
            end
        end
        -- boundary: the component is a black box (the lecture's
        -- "composable" discipline) — student wiring may enter it only
        -- at its initial state and leave it only at its final state
        local entry, exits = nil, {}
        for _, s in ipairs(sm.states) do
            local en = prefix .. tostring(s.name or s.id)
            if s.initial then entry = en end
            if s.accepting then exits[en] = true end
        end
        for _, e in ipairs(m.transitions or {}) do
            if not e.seed then
                local f = id_name[tostring(e.from)]
                local t = id_name[tostring(e.to)]
                if f and emb_set[f] and not exits[f] then
                    return { ok=false, kind="boundary",
                             msg="an edge leaves component " .. shown
                              .. ") at state " .. f .. " — leave a "
                              .. "component only via its final state" }
                end
                if t and emb_set[t] and t ~= entry then
                    return { ok=false, kind="boundary",
                             msg="an edge enters component " .. shown
                              .. ") at state " .. t .. " — enter a "
                              .. "component only via its initial "
                              .. "state" }
                end
            end
        end
        -- integration: every embedded state must lie on a path from
        -- the initial state to an accepting state (lambda steps count)
        local start, accs = nil, {}
        for _, s in ipairs(m.states) do
            local nm = tostring(s.name or s.id)
            if s.initial then start = nm end
            if s.accepting then accs[nm] = true end
        end
        local function bfs(from, g)
            local seen, q = {}, {from}
            if not from then return seen end
            seen[from] = true
            while #q > 0 do
                local u = table.remove(q, 1)
                for v,_ in pairs(g[u] or {}) do
                    if not seen[v] then seen[v] = true; q[#q+1] = v end
                end
            end
            return seen
        end
        local fwd = bfs(start, adj)
        local back = {}
        for a,_ in pairs(accs) do
            for v,_ in pairs(bfs(a, radj)) do back[v] = true end
        end
        for _, nm in ipairs(emb) do
            if not fwd[nm] or not back[nm] then
                return { ok=false, kind="disconnected",
                         msg="component " .. shown .. ") is not wired "
                          .. "into the automaton — state " .. nm
                          .. " lies on no accepting path" }
            end
        end
    end
    -- the composed automaton must itself be composable again — the
    -- lecture's invariant: exactly one initial state without incoming
    -- arrows, exactly one final state without outgoing arrows
    local cp = composable_problems(m)
    if cp then
        return { ok=false, kind="composable",
                 msg="not composable: " .. cp }
    end
    -- components check out: now the language, like a plain aut part
    local aut, problems = model_to_nfa(m, part.aut_type)
    if not aut then
        return { ok=false, kind="fail",
                 msg=table.concat(problems, "; ") }
    end
    if #problems > 0 then
        return { ok=false, kind="fail",
                 msg=table.concat(problems, ";  ") }
    end
    local ref = ref_any(part.reference)
    if part.complement then ref = complemented(ref) end
    local cmp, cex_s, cex_r = automata.compare_languages(aut, ref)
    if cmp ~= "=" then
        local parts = {}
        if cex_s then parts[#parts+1] = "'" .. word_or_lam(cex_s)
            .. "' is accepted but not in L" end
        if cex_r then parts[#parts+1] = "'" .. word_or_lam(cex_r)
            .. "' is in L but not accepted" end
        return { ok=false, kind="mismatch",
                 msg=table.concat(parts, ";  ") }
    end
    return { ok=true }
end

-- optional simplify slot: empty means "not attempted" (not a failure);
-- otherwise the language must match and the automaton should actually
-- be smaller than the composed one it was taken over from
function M.check_simplify(part, model_json, src_json)
    local ok, m = pcall(json.decode, model_json or "")
    if not ok or type(m) ~= "table"
       or not m.states or #m.states == 0 then
        return { ok=true, kind="empty",
                 msg="optional — 'take over' to simplify the automaton" }
    end
    local aut, problems = model_to_nfa(m, part.aut_type)
    if not aut then
        return { ok=false, kind="fail",
                 msg=table.concat(problems, "; ") }
    end
    if #problems > 0 then
        return { ok=false, kind="fail",
                 msg=table.concat(problems, ";  ") }
    end
    local ref = ref_any(part.reference)
    local cmp = automata.compare_languages(aut, ref)
    if cmp ~= "=" then
        return { ok=false, kind="mismatch",
                 msg="the simplified automaton changed the language" }
    end
    -- the result becomes the next stage's component, so it must keep
    -- the composable form (1 initial without incoming, 1 final
    -- without outgoing transitions) — except on the last step, where
    -- nothing embeds it: there a non-composable result is only a
    -- clear warning
    local cp = composable_problems(m)
    if cp then
        if part.last_step then
            return { ok=true, kind="warn",
                     msg="correct language — but NOT composable: " .. cp
                      .. ".  Fine as a final answer; only automata "
                      .. "that feed a later step must stay composable." }
        end
        return { ok=false, kind="composable",
                 msg="correct language, but not composable: " .. cp
                  .. " — it becomes the next step's component" }
    end
    local ok2, src = pcall(json.decode, src_json or "")
    if ok2 and type(src) == "table" and src.states then
        local n_new = #(m.states or {}) + #(m.transitions or {})
        local n_old = #(src.states or {}) + #(src.transitions or {})
        if n_new >= n_old then
            return { ok=true, kind="warn",
                     msg="correct language, but not simpler "
                      .. "than the composed automaton" }
        end
    end
    return { ok=true }
end

-- part.kind == "trace": the state sequence of the run on each word
function M.check_trace(part, traces)
    local ref = ref_dfa(part.reference)
    local rows, all_ok = {}, true
    for i, word in ipairs(part.words or {}) do
        local seq = {}
        for st in (traces and traces[i] or ""):gmatch("[%w_]+") do
            seq[#seq + 1] = st
        end
        if #seq == 0 then
            rows[i] = { kind="empty", msg="(empty)" }
        else
            local true_seq = run_states(ref, word)
            -- rows may give the full |w|+1-state run or omit the start
            -- state (|w| entries).  A dropped REPEAT mid-run also
            -- shortens the row by one — indistinguishable by length
            -- alone when the first symbol loops back to the start —
            -- so compare both alignments and keep the diagnosis that
            -- explains the longest prefix of the student's input
            local function diverge_at(sq)
                for j = 1, #true_seq do
                    if sq[j] ~= true_seq[j] then return j end
                end
            end
            local cands = { seq }
            if #seq == #true_seq - 1 then
                local ws = { true_seq[1] }
                for _, s in ipairs(seq) do ws[#ws + 1] = s end
                cands[2] = ws
            end
            local st_seq, diverge
            for _, sq in ipairs(cands) do
                if not diverge_at(sq) and #sq == #true_seq then
                    st_seq = sq; break
                end
            end
            if not st_seq then
                local best_d
                for _, sq in ipairs(cands) do
                    local d = diverge_at(sq)
                    if not d then st_seq = sq; diverge = nil; break end
                    if not best_d or d > best_d then
                        st_seq, diverge, best_d = sq, d, d
                    end
                end
            end
            if diverge then
                all_ok = false
                rows[i] = { kind="mismatch",
                    msg="first wrong at step " .. (diverge - 1)
                        .. ": after reading '" .. word:sub(1, diverge - 1)
                        .. "' the run is in " .. true_seq[diverge]
                        .. " (you wrote " .. tostring(st_seq[diverge] or "?")
                        .. ")" }
            elseif #st_seq ~= #true_seq then
                all_ok = false
                rows[i] = { kind="mismatch",
                    msg="run has " .. #true_seq - 1 .. " steps — "
                        .. "expected " .. #true_seq .. " states" }
            else
                rows[i] = { kind="ok" }
            end
        end
    end
    return { ok=all_ok, rows=rows }
end

-- part.kind == "accept": which of the words are accepted
function M.check_accept(part, answers)
    local ref = ref_dfa(part.reference)
    local rows, all_ok = {}, true
    for i, word in ipairs(part.words or {}) do
        local accepted = automata.is_accepted(ref, word)
        local student = answers and answers[i]
        -- the wire format uses "yes"/"no"/"" so unset cells survive as
        -- a dense JSON array; booleans work too
        if student == "yes" then student = true
        elseif student == "no" then student = false
        elseif student == "" then student = nil end
        if student == nil then
            all_ok = false
            rows[i] = { kind="empty", msg="(unanswered)" }
        elseif student == accepted then
            rows[i] = { kind="ok",
                msg = accepted and "accepted ✓" or "rejected ✓" }
        else
            all_ok = false
            rows[i] = { kind="mismatch",
                msg = accepted and "this word IS accepted"
                              or "this word is NOT accepted" }
        end
    end
    return { ok=all_ok, rows=rows }
end

-- part.kind == "table": transition table entries δ(state, sym) = name
function M.check_table(part, cells)
    local ref = ref_dfa(part.reference)
    local cellres, all_ok = {}, true
    for i, q in ipairs(part.states or {}) do
        for _, sym in ipairs(part.alphabet or {}) do
            local want = ref:get_to_states(q, sym)
            local got = cells and cells[i .. "|" .. sym]
            if not (got and got ~= "") then
                all_ok = false
                cellres[i .. "|" .. sym] = { kind="empty", msg="" }
            elseif got == want then
                cellres[i .. "|" .. sym] = { kind="ok" }
            else
                all_ok = false
                cellres[i .. "|" .. sym] = { kind="mismatch" }
            end
        end
    end
    return { ok=all_ok, cells=cellres }
end

-- part.kind == "regexp": delegate to the 1.2 checker (part.reference is
-- the reference regexp string)
function M.check_regexp(part, expr)
    return RC.check(part, expr)
end

-- ---------------- state-set answers ----------------
-- tolerant set syntax: "{q0,q2}", "q0,q2", "q0 q2", "∅", "{}" all work;
-- returns the name->true table
local function parse_state_set(s)
    local set = {}
    s = (s or ""):gsub("[{}%(%)]", "")
    for tok in s:gmatch("[%w_]+") do set[tok] = true end
    return set
end

-- "{q0,q2}" | "∅" for messages
local function set_string(set)
    local names = {}
    for s, _ in pairs(set) do names[#names + 1] = tostring(s) end
    table.sort(names)
    if #names == 0 then return "∅" end
    return "{" .. table.concat(names, ",") .. "}"
end

-- want/got are name->true tables; returns nil if equal, else a
-- diff message ("missing q1; extra q3")
local function set_diff(want, got)
    local missing, extra = {}, {}
    for s, _ in pairs(want) do
        if not got[s] then missing[#missing + 1] = s end
    end
    for s, _ in pairs(got) do
        if not want[s] then extra[#extra + 1] = s end
    end
    if #missing == 0 and #extra == 0 then return nil end
    local parts = {}
    if #missing > 0 then
        parts[#parts + 1] = "missing " .. table.concat(missing, ",")
    end
    if #extra > 0 then
        parts[#parts + 1] = "extra " .. table.concat(extra, ",")
    end
    return table.concat(parts, ";  ")
end

-- part.kind == "closure": λ-closure(qi) per state of the reference NFA
function M.check_closure(part, sets)
    local nfa = ref_any(part.reference)
    local rows, all_ok = {}, true
    for i, q in ipairs(part.states or {}) do
        local want = automata.lambda_closure(nfa, q)
        local got_s = sets and sets[i]
        if not (got_s and got_s:match("%S")) then
            all_ok = false
            rows[i] = { kind="empty", msg="(unanswered)" }
        else
            local diff = set_diff(want, parse_state_set(got_s))
            if diff then
                all_ok = false
                rows[i] = { kind="mismatch",
                    msg="should be " .. set_string(want)
                        .. "  (" .. diff .. ")" }
            else
                rows[i] = { kind="ok" }
            end
        end
    end
    return { ok=all_ok, rows=rows }
end

-- part.kind == "stable": the input transition function t(q,a) of the
-- reference NFA(-λ) — cells are state SETS, evaluated through
-- state_set_step_lambda (λ-closure before and after the step)
function M.check_stable(part, cells)
    local nfa = ref_any(part.reference)
    local cellres, all_ok = {}, true
    for i, q in ipairs(part.states or {}) do
        for _, sym in ipairs(part.alphabet or {}) do
            local qset = nfa:make_state_set()
            qset[q] = true
            local want = automata.state_set_step_lambda(nfa, qset, sym)
            local got = cells and cells[i .. "|" .. sym]
            if not (got and got:match("%S")) then
                all_ok = false
                cellres[i .. "|" .. sym] = { kind="empty", msg="" }
            else
                local diff = set_diff(want, parse_state_set(got))
                if diff then
                    all_ok = false
                    cellres[i .. "|" .. sym] = { kind="mismatch",
                        msg=set_string(want) }
                else
                    cellres[i .. "|" .. sym] = { kind="ok" }
                end
            end
        end
    end
    return { ok=all_ok, cells=cellres }
end

-- ==================== sheet 3 part kinds ====================

-- part.kind == "choice": one <select> per declared slot; the task
-- supplies part.sel_check(sel) -> result (sel[slotkey] = option id)
function M.check_choice(part, sel)
    if type(part.sel_check) ~= "function" then
        return { ok=false, kind="fail", msg="no checker configured" }
    end
    sel = sel or {}
    for _, slot in ipairs(part.slots or {}) do
        local v = sel[slot.key]
        if v == nil or v == "" then
            return { ok=false, kind="empty",
                     msg="make a choice for " .. slot.label }
        end
    end
    return part.sel_check(sel)
end

-- part.kind == "pumping": the adversary game — see wordproof/pumping.lua
local PUMP = require "wordproof.pumping"
function M.check_pumping(part, z, is_tbl, k, gen)
    return PUMP.check(part.lang, z, is_tbl, k or part.pump_k, gen, part)
end
function M.pump_splits(part, z, k)
    return PUMP.instantiate(part.lang, z, k or part.pump_k)
end

-- ---------------- DFA minimisation ----------------

-- distinguishable unordered state pairs of the reference DFA.
-- returns D ("qi|qj" -> true, i<j order via key()) and the key fn
function M.dfa_distinguishable(reference, states)
    local dfa = ref_dfa(reference)
    local alpha = {}
    for s, _ in pairs(dfa:get_symbols()) do alpha[#alpha + 1] = s end
    table.sort(alpha)
    local function key(a, b)
        return (a < b) and (a .. "|" .. b) or (b .. "|" .. a)
    end
    local D = {}
    for i = 1, #states do
        for j = i + 1, #states do
            if dfa:is_accepting(states[i])
               ~= dfa:is_accepting(states[j]) then
                D[key(states[i], states[j])] = true
            end
        end
    end
    local grew = true
    while grew do
        grew = false
        for i = 1, #states do
            for j = i + 1, #states do
                local p, q = states[i], states[j]
                if not D[key(p, q)] then
                    for _, sym in ipairs(alpha) do
                        local a = dfa:get_to_states(p, sym)
                        local b = dfa:get_to_states(q, sym)
                        if a and b and a ~= b and D[key(a, b)] then
                            D[key(p, q)] = true
                            grew = true
                            break
                        end
                    end
                end
            end
        end
    end
    return D, key
end

-- equivalence classes: states grouped by ~ (not distinguishable)
function M.dfa_equiv_classes(reference, states)
    local D, key = M.dfa_distinguishable(reference, states)
    local cls = {}
    for _, s in ipairs(states) do
        local hit
        for _, c in ipairs(cls) do
            if not D[key(c[1], s)] then hit = c break end
        end
        if hit then hit[#hit + 1] = s else cls[#cls + 1] = { s } end
    end
    return cls
end

local function run_from(dfa, s, w)
    local cur = s
    for i = 1, #w do
        cur = dfa:get_to_states(cur, w:sub(i, i))
        if not cur then return nil end
    end
    return cur
end

-- part.kind == "min_table": mark the distinguishable pairs, give a
-- distinguishing word for each marked pair, and list the
-- equivalence classes.  marks = {"i|j",...}, wit = {"i|j" -> word},
-- classes_str = "{q0,q3} {q1,q4} ..." (groups may also be /-separated)
function M.check_min_table(part, marks, classes_str, wit)
    local dfa = ref_dfa(part.reference)
    local states = part.states or {}
    local D, key = M.dfa_distinguishable(part.reference, states)
    local smark = {}
    for _, k in ipairs(marks or {}) do smark[k] = true end
    local cells, rows, all_ok = {}, {}, true
    -- verdict per pair cell (enumeration index = row key)
    local wi = 0
    for i = 1, #states do
        for j = i + 1, #states do
            wi = wi + 1
            local a, b = states[i], states[j]
            local k = key(a, b)
            local truth, said = D[k] and true or false,
                                smark[k] and true or false
            if truth and not said then
                all_ok = false
                cells[k] = { kind = "mismatch",
                             msg = "distinguishable — mark it" }
            elseif said and not truth then
                all_ok = false
                cells[k] = { kind = "mismatch",
                             msg = "these states are equivalent" }
            else
                cells[k] = { kind = "ok" }
            end
            -- a distinguishing word is required for every marked pair
            if said then
                local w = wit and wit[k]
                if not truth then
                    all_ok = false
                    rows[wi] = { kind = "mismatch",
                        msg = "no word can distinguish " .. a .. ","
                            .. b .. " — they are equivalent" }
                elseif w == nil then
                    all_ok = false
                    rows[wi] = { kind = "empty",
                                 msg = "distinguishing word?" }
                else
                    -- "λ"/"ε"/spaces may stand for the empty word,
                    -- which is a legal witness for acc/non-acc pairs
                    w = w:gsub("%s", ""):gsub("λ", ""):gsub("ε", "")
                    local ea = run_from(dfa, a, w)
                    local eb = run_from(dfa, b, w)
                    local acca = ea and dfa:is_accepting(ea) or false
                    local accb = eb and dfa:is_accepting(eb) or false
                    if acca ~= accb then
                        rows[wi] = { kind = "ok" }
                    else
                        all_ok = false
                        rows[wi] = { kind = "mismatch",
                            msg = "'" .. w .. "' does not distinguish "
                                .. a .. " and " .. b }
                    end
                end
            end
        end
    end
    -- equivalence classes as a partition of the state set
    local groups = {}
    local gs = (classes_str or ""):gsub("[%(%)]", "")
    if gs:find("{") then
        for g in gs:gmatch("{([^{}]*)}") do
            groups[#groups + 1] = parse_state_set(g)
        end
    else
        for g in gs:gmatch("[^/;]+") do
            local st = parse_state_set(g)
            if next(st) then groups[#groups + 1] = st end
        end
    end
    if #groups == 0 then
        all_ok = false
        cells.classes = { kind = "mismatch",
                          msg = "list the classes, e.g. {q0,q3} {q1}" }
    else
        local seen, class_of = {}, {}
        local perr
        for _, g in ipairs(groups) do
            for s in pairs(g) do
                if seen[s] then
                    perr = s .. " appears in two classes"
                end
                seen[s] = true
                class_of[s] = g
            end
        end
        if not perr then
            for _, s in ipairs(states) do
                if not seen[s] then
                    perr = s .. " is missing"
                    break
                end
            end
        end
        if not perr then
            for i = 1, #states do
                for j = i + 1, #states do
                    local a, b = states[i], states[j]
                    if class_of[a] == class_of[b] and D[key(a, b)] then
                        perr = a .. " and " .. b
                            .. " are distinguishable but in one class"
                        break
                    elseif class_of[a] ~= class_of[b]
                           and not D[key(a, b)] then
                        perr = a .. " and " .. b
                            .. " are equivalent but split apart"
                        break
                    end
                end
                if perr then break end
            end
        end
        if perr then
            all_ok = false
            cells.classes = { kind = "mismatch", msg = perr }
        else
            cells.classes = { kind = "ok" }
        end
    end
    if all_ok then
        return { ok = true, kind = "ok", cells = cells, rows = rows }
    end
    return { ok = false, kind = "fail", cells = cells, rows = rows,
             msg = "mark the distinguishable pairs, justify each "
                .. "with a word, and give the equivalence classes" }
end

M._model_to_dfa = model_to_dfa   -- exposed for tests
M._model_to_nfa = model_to_nfa

return M
