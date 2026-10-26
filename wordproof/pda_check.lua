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

function M.check_pda(part, text)
    local pda, err, warn = M.parse_pda_text(text)
    if not pda then return { ok = false, msg = err } end
    local notes = warn and { warn } or {}
    if part.deterministic then
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
    local ok, cmp, cex1, cex2 = pcall(
        automata.compare_languages, ref, pda)
    if not ok then
        return { ok = false, msg = "comparison failed: "
            .. tostring(cmp) }
    end
    if cmp == "=" then
        return { ok = true, msg = "✓ languages are equal"
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

return M
