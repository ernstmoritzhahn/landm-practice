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

-- decoded editor model -> dfa, problems | nil, problems (unusable)
local function model_to_dfa(m, expect_type)
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
    -- totality (DFA only)
    if not is_nfa_type(expect_type) then
        local syms = {}
        for s, _ in pairs(dfa:get_symbols() or {}) do
            syms[#syms + 1] = s
        end
        for _, nm in ipairs(names) do
            for _, sym in ipairs(syms) do
                if not seen[nm .. "\0" .. sym] then
                    problems[#problems + 1] = "missing " .. sym
                        .. "-transition from " .. nm
                end
            end
        end
    end
    return dfa, problems
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
    local aut, problems
    if is_nfa_type(part.aut_type) then
        aut, problems = model_to_nfa(m, part.aut_type)
    else
        aut, problems = model_to_dfa(m, part.aut_type)
    end
    if not aut then
        return { ok=false, kind="fail", msg=table.concat(problems,"; ") }
    end
    if #problems > 0 then
        return { ok=false, kind="fail",
                 msg=table.concat(problems, ";  ") }
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
                 msg=table.concat(parts, ";  ") }
    end
    if not is_tuple or is_nfa_type(part.aut_type) then
        return { ok=true }
    end
    local n_student, n_ref = 0, 0
    for _ in pairs(aut:get_states()) do n_student = n_student + 1 end
    for _ in pairs(ref:get_states()) do n_ref = n_ref + 1 end
    if n_student ~= n_ref then
        return { ok=false, kind="warn",
                 msg="accepts the right language, but M has " .. n_ref
                  .. " states — yours has " .. n_student }
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

M._model_to_dfa = model_to_dfa   -- exposed for tests
M._model_to_nfa = model_to_nfa

return M
