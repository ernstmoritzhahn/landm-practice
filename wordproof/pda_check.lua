-- wordproof/pda_check.lua — check student PDAs entered as transition
-- lists.  One transition per line:
--     q0, a λ/A, q1        (input a, pop λ, push A)
--     q1 -b A/λ-> q2       (arrow form also accepted)
-- Declarations: "start: q0", "final: q1 q3".
-- part = { kind="pda", pda_ref=PDA|fn, deterministic=bool,
--          max_stack=n, alphabet={...} }
local util = require "lib.util"
local automata = require "automata"
local trim, split = util.trim, util.split

local M = {}

local function norm_sym(s)
    s = trim(s or "")
    s = s:gsub("λ", ""):gsub("\\", "/")
    return s
end

-- parse one label "input pop/push" into a label string for
-- pda:add_transition; returns nil, err on bad syntax
local function parse_line(line)
    -- declaration?
    local key, rest = line:match("^(%a+)%s*:%s*(.-)%s*$")
    if key then
        return { decl = key:lower(), rest = rest }
    end
    local from, label, to =
        line:match("^(.-)%s*[,;]%s*(.-)%s*[,;]%s*(.-)%s*$")
    if not from then
        from, label, to =
            line:match("^(%S+)%s*%-+>?%s*(.-)%s*%-+>%s*(%S+)%s*$")
        if not from then
            from, label, to =
                line:match("^(%S+)%s+(.*%S)%s+%-?>?%s*(q?%w+)%s*$")
        end
    end
    if not from or from == "" or not to or to == "" or not label then
        return nil, "expected 'state, input pop/push, state'"
    end
    return { from = trim(from), label = trim(label), to = trim(to) }
end

-- build an extended PDA from student text
function M.parse_pda_text(text)
    local pda = automata.make_pda(true)
    local initial, finals, err_line, state_set = nil, {}, nil, {}
    for _, raw in ipairs(split(text or "", "\n")) do
        local line = trim(raw:gsub("%-%-.*$", ""))
        if line ~= "" then
            local t, perr = parse_line(line)
            if not t then
                err_line = "line '" .. line .. "': " .. perr
                break
            elseif t.decl then
                if t.decl == "start" or t.decl == "initial" then
                    initial = trim((split(t.rest, "%s")[1]))
                    if initial ~= "" and not state_set[initial] then
                        state_set[initial] = true
                        pda:add_state(initial)
                    end
                elseif t.decl == "final" or t.decl == "accept"
                        or t.decl == "accepting" then
                    for _, s in ipairs(split(t.rest, "[%s,]+")) do
                        s = trim(s)
                        if s ~= "" then
                            finals[#finals + 1] = s
                            if not state_set[s] then
                                state_set[s] = true
                                pda:add_state(s)
                            end
                        end
                    end
                else
                    err_line = "unknown declaration '" .. t.decl .. ":'"
                    break
                end
            else
                if not state_set[t.from] then
                    state_set[t.from] = true
                    pda:add_state(t.from)
                end
                if not state_set[t.to] then
                    state_set[t.to] = true
                    pda:add_state(t.to)
                end
                for _, lab in ipairs(split(t.label, "|")) do
                    lab = trim(lab:gsub("\\", "/"))
                    local ok, perr = pcall(
                        pda.add_transition, pda, t.from, lab, t.to)
                    if not ok then
                        err_line = "line '" .. line .. "': "
                            .. tostring(perr)
                        break
                    end
                end
            end
        end
        if err_line then break end
    end
    if err_line then return nil, err_line end
    if not initial then
        return nil, "no start state declared (add a 'start: q0' line)"
    end
    pda:set_initial(initial, true)
    if #finals == 0 then
        -- acceptance by empty stack is the default in the book; also
        -- allow it explicitly when the part expects empty-stack
        return pda, nil, "no final states declared — accepts by "
            .. "empty stack (add 'final: ...' to accept by state)"
    end
    for _, s in ipairs(finals) do pda:set_accepting(s, true) end
    return pda
end

-- iterate transitions as {from,label={input,pop,push},to}
local function each_transition(pda)
    local out = {}
    for _, t in ipairs(pda.transitions or {}) do
        out[#out + 1] = t
    end
    if #out == 0 and pda.get_transitions then
        for _, t in ipairs(pda:get_transitions()) do out[#out + 1] = t end
    end
    return out
end

-- Sudkamp determinism: two transitions from the same state conflict
-- when their inputs can apply together (equal, or either is λ) AND
-- their pop conditions can hold together (equal, or either is λ).
function M.is_deterministic(pda)
    local by_state = {}
    for _, t in ipairs(each_transition(pda)) do
        local f = t.from
        by_state[f] = by_state[f] or {}
        by_state[f][#by_state[f] + 1] = t
    end
    for st, ts in pairs(by_state) do
        for i = 1, #ts do
            for j = i + 1, #ts do
                local a, b = ts[i].label, ts[j].label
                local input_clash =
                    a.input == b.input or a.input == "" or b.input == ""
                local pop_clash =
                    a.pop == b.pop or a.pop == "" or b.pop == ""
                if input_clash and pop_clash then
                    return false, string.format(
                        "nondeterministic in state %s: "
                        .. "'%s' and '%s' can both apply",
                        st, tostring(a), tostring(b))
                end
            end
        end
    end
    return true
end

local function stack_symbol_count(pda)
    local n = 0
    for _ in pairs(pda.stack_symbols or {}) do n = n + 1 end
    if n == 0 and pda.get_stack_symbols then
        for _ in pairs(pda:get_stack_symbols()) do n = n + 1 end
    end
    return n
end

local REL_DISPLAY = { ["="] = "=", ["!="] = "≠", ["<"] = "⊊",
                      [">"] = "⊋" }

-- shared tail for the text and the graphical model paths: `pda` is a
-- built make_pda object, `notes` accumulates student-facing warnings,
-- `atype` is the effective type name (part.aut_type wins — the task
-- sets the contract; the saved model's own type is only the fallback
-- for callers without one, "pda" the default)
local function check_pda_obj(part, pda, notes, atype)
    notes = notes or {}
    -- the pda family's acceptance mode comes from the type name
    -- (dpda-* deterministic, -* suffix picks L_F/L_E; anything else
    -- keeps the plain L(M) semantics — both conditions).  The mode
    -- is stamped onto the automaton objects; the word problem reads
    -- it back per configuration.
    local label_lang = require "automata.label_lang"
    atype = part.aut_type or atype or "pda"
    local mode = label_lang.pda_accept
                 and label_lang.pda_accept(atype) or "fe"
    pda.pda_acceptance = mode
    -- deterministic variants demand Sudkamp determinism even when the
    -- part does not spell it out — the type name is the requirement
    local want_det = part.deterministic
                     or (label_lang.is_det_pda
                         and label_lang.is_det_pda(atype))
    if want_det then
        local det, derr = M.is_deterministic(pda)
        if not det then
            return { ok = false,
                     msg = derr
                         .. " — the PDA must be deterministic" }
        end
    end
    if part.max_stack then
        local n = stack_symbol_count(pda)
        if n > part.max_stack then
            return { ok = false, msg = string.format(
                "%d stack symbols used, at most %d allowed",
                n, part.max_stack) }
        end
    end
    local ref = part.pda_ref
    if type(ref) == "function" then ref = ref() end
    if not ref then return { ok = false, msg = "no reference PDA" } end
    -- both sides run under the part's acceptance mode — comparing an
    -- L_E reference against an L(M) student would be meaningless
    ref.pda_acceptance = mode
    -- bounded comparison: PDA equivalence is undecidable, so the
    -- bounded search runs under a CPU deadline — in the wasm worker a
    -- stack-growing student PDA would otherwise grind for minutes
    local budget = part.time_budget or 12
    local ok, cmp, cex1, cex2, trunc = pcall(
        automata.compare_languages, ref, pda, os.clock() + budget)
    if not ok then
        return { ok = false, msg = "comparison failed: "
            .. tostring(cmp) }
    end
    if cmp == "=" then
        return { ok = true, msg = (trunc
                and "✓ no difference found (bounded search)"
                or  "✓ languages are equal")
            .. (#notes > 0 and (" — " .. table.concat(notes, "; "))
                or "") }
    end
    local bits = {}
    if cmp and REL_DISPLAY[cmp] then
        bits[#bits + 1] = "the languages differ (ℒ(ref) "
            .. REL_DISPLAY[cmp] .. " ℒ(yours))"
    else
        bits[#bits + 1] = "the languages differ"
    end
    local function wtxt(w)
        w = tostring(w)
        return w == "" and "λ" or w
    end
    if cex1 then
        bits[#bits + 1] = "'" .. wtxt(cex1)
            .. "' is accepted by the reference but not by yours"
    end
    if cex2 then
        bits[#bits + 1] = "'" .. wtxt(cex2)
            .. "' is accepted by yours but not by the reference"
    end
    return { ok = false, msg = table.concat(bits, "; ") }
end

-- graphical input: the editor's model JSON ({type="pda", states,
-- transitions[{from,to,label}]}) — every label parses through
-- automata.label_lang ("input pop/push" / "input, pop -> push")
function M.check_pda_model(part, model_json)
    local json = require "lib.json"
    local label_lang = require "automata.label_lang"
    local ok, m = pcall(json.decode, model_json or "")
    if not ok or type(m) ~= "table" or not m.states
       or #m.states == 0 then
        return { ok=false, msg = "no automaton — draw the state diagram" }
    end
    local pda = automata.make_pda(true)
    local names, initial, problems = {}, nil, {}
    for _, s in ipairs(m.states) do
        local nm = tostring(s.name or s.id)
        names[s.id] = nm
        pda:add_state(nm)
        if s.initial then
            if initial then
                problems[#problems + 1] = "more than one initial state"
            else
                initial = nm
            end
        end
        if s.accepting then pda:set_accepting(nm, true) end
    end
    for _, e in ipairs(m.transitions or {}) do
        local a, b = names[e.from], names[e.to]
        if not (a and b) then
            problems[#problems + 1] = "transition with a dangling "
                .. "endpoint"
        else
            local ts, why = label_lang.parse_many("pda", e.label)
            if not ts then
                problems[#problems + 1] = "label '" .. tostring(e.label)
                    .. "': " .. why
            else
                for _, t in ipairs(ts) do
                    local pok, perr = pcall(pda.add_transition, pda, a,
                                            label_lang.pda_label(t), b)
                    if not pok then
                        -- drop the "[string "..."]:NN:" source prefix —
                        -- internal chunk locations mean nothing here
                        local msg = tostring(perr):gsub(
                            '^%[string "[^"]*"%]:%d+:%s*', "")
                        if msg:find("input character") then
                            msg = "input must be a single "
                                .. "symbol or λ"
                        elseif msg:find("pop character") then
                            msg = "pop must be a single stack "
                                .. "symbol or λ (push may be "
                                .. "longer)"
                        end
                        problems[#problems + 1] = "label '"
                            .. label_lang.pda_label(t) .. "': " .. msg
                    end
                end
            end
        end
    end
    if not initial then
        problems[#problems + 1] = "no initial state"
    else
        pda:set_initial(initial, true)
    end
    if #problems > 0 then
        return { ok = false, msg = table.concat(problems, "; ") }
    end
    local notes = {}
    if not next(pda:get_accepting() or {}) then
        notes[1] = "no final states — accepts by empty stack"
    end
    return check_pda_obj(part, pda, notes, m.type)
end

function M.check_pda(part, text)
    local pda, err, warn = M.parse_pda_text(text)
    if not pda then return { ok = false, msg = err } end
    local notes = warn and { warn } or {}
    return check_pda_obj(part, pda, notes)
end

return M
