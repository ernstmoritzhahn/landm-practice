-- wordproof/grammar_check.lua — grading for the sheet-4 grammar
-- parts: free-form grammar input (parse_rules + language equality,
-- the same machinery the exam grader uses), derivation chains
-- (optionally leftmost/rightmost), derivation trees in bracket
-- notation, and set-notation patterns checked by two-sided
-- enumeration.
--
-- Reuses automata.* throughout: parse_rules, grammar_compare_languages
-- (certified where decidable, honest "undecided" otherwise),
-- grammar_to_nfa + compare_languages for regular targets, and the
-- single-step successors machinery for derivation verification.

require("lib.util").fix_path()
local automata = require "automata"

local M = {}

local function fail(msg, kind)
    return { ok = false, kind = kind or "fail", msg = msg }
end

-- ---------- grammar parsing ----------

local gcache = {}
local function grammar_of(text, opts)
    local key = text .. "\0" .. (opts and opts.start or "")
    if gcache[key] then return gcache[key] end
    local g, bad = automata.parse_rules(text,
        opts and { start_variable_explicit = opts.start } or nil)
    local res = { g = g, bad = bad }
    gcache[key] = res
    return res
end

local function is_linear(grammar)
    -- returns "right", "left" or nil; rhs ∈ Σ* V? or V? Σ*
    local vars = grammar:get_variables()
    local right, left = true, true
    for rule, _ in pairs(grammar:get_rules()) do
        if rule.lhs:len() ~= 1
            or not vars[rule.lhs:get_char(1)] then
            return nil
        end
        for i = 1, rule.rhs:len() do
            if vars[rule.rhs:get_char(i)] then
                if i ~= rule.rhs:len() then right = false end
                if i ~= 1 then left = false end
            end
        end
    end
    if right then return "right" end
    if left then return "left" end
    return nil
end

-- ---------- grammar part ----------

-- part.grammar_ref: reference grammar text  OR
-- part.aut_ref:     reference automaton (regular language)
-- part.right_linear / part.context_free: shape requirements
function M.check_grammar(part, text)
    text = text or ""
    if not text:match("%S") then
        return fail("enter the grammar — one rule per line, e.g. "
            .. "S -> aA | b", "empty")
    end
    local pr = grammar_of(text,
        { start = part.start_variable })
    local g = pr.g
    if not (g and #g:get_rules() > 0) then
        return fail("no rules found — write e.g.  S -> aA | b",
            "parse")
    end
    if part.right_linear or part.regular then
        local lin = is_linear(g)
        if not lin then
            return fail("not a regular grammar — every rule must be "
                .. "X -> w or X -> wY (right-linear), or the "
                .. "left-linear mirror")
        end
        part._lin = lin
    end
    if part.context_free and not automata.grammar_is_context_free(g) then
        return fail("not context-free: a rule's left side must be a "
            .. "single variable")
    end
    if part.aut_ref then
        -- language of a regular grammar vs a reference automaton
        local lin = part._lin or is_linear(g)
        if not lin then
            return fail("the grammar is not linear — its language "
                .. "cannot be checked against the automaton")
        end
        local ref = part.aut_ref
        if type(ref) == "function" then ref = ref() end
        local nfa = automata.grammar_to_nfa(g, lin == "left")
        local cmp, cex_s, cex_r =
            automata.compare_languages(nfa, ref)
        if cmp == "=" then
            return { ok = true }
        end
        local bits = {}
        if cex_s then bits[#bits + 1] = "'" .. (cex_s ~= "" and cex_s
            or "λ") .. "' is derived but not in L(M)" end
        if cex_r then bits[#bits + 1] = "'" .. (cex_r ~= "" and cex_r
            or "λ") .. "' is in L(M) but not derived" end
        return fail(table.concat(bits, ";  "), "mismatch")
    end
    if part.grammar_ref then
        local ref = grammar_of(part.grammar_ref).g
        local cmp, cex_s, cex_r = automata.grammar_compare_languages(
            ref, g, { max_words = 400, max_length = 12,
                      deadline = os.clock() + 10 })
        if cmp == "=" then
            return { ok = true,
                     msg = "L(G) correct — verified" }
        end
        local bits = {}
        if cex_s then bits[#bits + 1] = "'" .. (cex_s ~= "" and cex_s
            or "λ") .. "' ∈ target but not derivable" end
        if cex_r then bits[#bits + 1] = "'" .. (cex_r ~= "" and cex_r
            or "λ") .. "' is derivable but ∉ target" end
        if cmp then
            return fail(table.concat(bits, ";  "), "mismatch")
        end
        if part.bounded_ok then
            -- type-0 grammars: equality is undecidable in general —
            -- fall back to two-sided sampling over short words
            local maxl, bad, n = 8, nil, 0
            local ref_words = automata.grammar_enumerate_words(
                ref, maxl) or {}
            local stu_words = automata.grammar_enumerate_words(
                g, maxl) or {}
            for w in pairs(ref_words) do
                n = n + 1
                local has = automata.grammar_contains_word(w, g)
                if has ~= true then
                    bad = "'" .. (w == "" and "λ" or w)
                        .. "' ∈ target but not derived"
                    break
                end
            end
            if not bad then
                for w in pairs(stu_words) do
                    n = n + 1
                    local has = automata.grammar_contains_word(w, ref)
                    if has ~= true then
                        bad = "'" .. (w == "" and "λ" or w)
                            .. "' derived but ∉ target"
                        break
                    end
                end
            end
            if bad then return fail(bad, "mismatch") end
            return { ok = true,
                     msg = "✓ consistent on all derivable words "
                        .. "up to length " .. maxl .. " (" .. n
                        .. " words compared — unrestricted "
                        .. "grammars admit no decision procedure, "
                        .. "so this is a bounded check)" }
        end
        return { ok = false, kind = "warn",
                 msg = "could not decide language equality within "
                    .. "the search budget — check by hand" }
    end
    return { ok = true }
end

-- ---------- derivation part ----------

local function tokenise_form(s, grammar)
    s = (s or ""):gsub("%s", ""):gsub("λ", ""):gsub("ε", "")
    return automata.tokenise_word(s)
end

-- split the textarea into sentential forms: newline- or
-- arrow-separated (the separator set covers =>, ->, ⇒, →)
local function split_forms(text)
    local forms = {}
    for line in (text or ""):gmatch("[^\n]+") do
        line = line:gsub("=>", "\30"):gsub("->", "\30")
            :gsub("⇒", "\30"):gsub("→", "\30"):gsub("↦", "\30")
        for piece in line:gmatch("[^\30]+") do
            local f = piece:gsub("%s", "")
            if f ~= "" then forms[#forms + 1] = f end
        end
    end
    return forms
end

-- every (rule, position) witnessing prev ⇒ cur in one step
local function step_positions(prev, cur, grammar)
    local hits = {}
    local target = tostring(cur)
    for rule, _ in pairs(grammar:get_rules()) do
        for pos, _ in pairs(
                automata.grammar_rule_matches(prev, rule)) do
            if tostring(automata.grammar_rule_apply(
                    prev, rule, pos)) == target then
                hits[#hits + 1] = pos
            end
        end
    end
    return hits
end

local function var_positions(form, vars)
    local first, last
    for i = 1, form:len() do
        if vars[form:get_char(i)] then
            first = first or i
            last = i
        end
    end
    return first, last
end

local function check_chain(forms, grammar, mode)
    if #forms < 2 then
        return nil, "a derivation needs at least a start line and "
            .. "the final word"
    end
    local start = grammar:get_start_variable()
    if forms[1] ~= tostring(start) then
        return nil, "start with the start variable " .. tostring(start)
    end
    local vars = grammar:get_variables()
    local prev = tokenise_form(forms[1])
    for i = 2, #forms do
        local cur = tokenise_form(forms[i])
        local hits = step_positions(prev, cur, grammar)
        if #hits == 0 then
            return nil, "line " .. i .. " ('" .. forms[i] .. "') is "
                .. "not reachable from '" .. forms[i - 1]
                .. "' in one step"
        end
        if mode ~= "any" then
            local fv, lv = var_positions(prev, vars)
            local ok = false
            for _, pos in ipairs(hits) do
                if (mode == "leftmost" and pos == fv)
                    or (mode == "rightmost" and pos == lv) then
                    ok = true; break
                end
            end
            if not ok then
                return nil, "line " .. i .. ": the step '"
                    .. forms[i - 1] .. " → " .. forms[i]
                    .. "' is not " .. mode .. " (you rewrote "
                    .. "a variable that is not the "
                    .. (mode == "leftmost" and "leftmost"
                        or "rightmost") .. " one)"
            end
        end
        prev = cur
    end
    return prev
end

-- part: {grammar=text, target=word, mode="any|leftmost|rightmost",
--        count=N, distinct=bool}
-- input: list of textarea strings (one per derivation)
function M.check_derivation(part, texts)
    local pr = grammar_of(part.grammar or "")
    local grammar = pr.g
    local want = part.count or 1
    texts = texts or {}
    local ends = {}
    for d = 1, want do
        local text = texts[d] or ""
        if not text:match("%S") then
            return fail("derivation " .. (want > 1
                and ("#" .. d .. " ") or "") .. "is empty", "empty")
        end
        local forms = split_forms(text)
        local final, err = check_chain(forms, grammar,
            part.mode or "any")
        if not final then
            return fail((want > 1 and ("derivation #" .. d .. ": ")
                or "") .. err)
        end
        ends[d] = tostring(final)
    end
    local target = (part.target or ""):gsub("%s", "")
    for d = 1, want do
        if ends[d] ~= target then
            return fail("derivation " .. (want > 1
                and ("#" .. d .. " ") or "") .. "ends in '"
                .. (ends[d] ~= "" and ends[d] or "λ")
                .. "', not '" .. (target ~= "" and target or "λ")
                .. "'")
        end
    end
    if part.distinct and want >= 2 then
        local same = true
        local base = split_forms(texts[1])
        for d = 2, want do
            local other = split_forms(texts[d])
            if #other ~= #base then same = false; break end
            for i = 1, #base do
                if other[i] ~= base[i] then same = false end
            end
            if not same then break end
        end
        if same then
            return fail("the two derivations are identical — that "
                .. "does not show ambiguity")
        end
    end
    return { ok = true }
end

-- ---------- derivation tree (bracket notation) ----------
--   S(a b S(A(c A(c d) d)) c c)   —  label(children) per node,
--   a λ leaf is written A() or A(λ); terminals are bare leaves.

local function parse_tree(s)
    local i, n = 1, #s
    local function ws() while i <= n and s:sub(i, i):match("%s")
        do i = i + 1 end end
    local function node()
        ws()
        if i > n then return nil, "unexpected end" end
        local c = s:sub(i, i)
        if c == "(" or c == ")" or c == "," then
            return nil, "expected a symbol, got '" .. c .. "'"
        end
        -- symbols are single UTF-8 chars (λ, subscripts are typed
        -- as base letter + digit, e.g. Q0 → two chars is fine only
        -- for the multi-char path below)
        local b = c:byte()
        if b >= 0xF0 then c = s:sub(i, i + 3); i = i + 3
        elseif b >= 0xE0 then c = s:sub(i, i + 2); i = i + 2
        elseif b >= 0xC0 then c = s:sub(i, i + 1); i = i + 1 end
        local nd = { sym = c, children = {} }
        i = i + 1
        ws()
        if s:sub(i, i) == "(" then
            i = i + 1
            while true do
                ws()
                if i > n then return nil, "missing ')'" end
                if s:sub(i, i) == ")" then i = i + 1; break end
                if s:sub(i, i) == "," then i = i + 1
                else
                    local child, err = node()
                    if not child then return nil, err end
                    nd.children[#nd.children + 1] = child
                end
            end
        end
        return nd
    end
    local t, err = node()
    if not t then return nil, err end
    ws()
    if i <= n then return nil, "trailing '" .. s:sub(i) .. "'" end
    return t
end

local function check_tree_node(nd, grammar, vars, syms)
    local kids = nd.children
    if #kids == 0 then
        if vars[nd.sym] then
            -- bare variable leaf = A ⇒ λ, requires an A→λ rule
            for rule, _ in pairs(grammar:get_rules()) do
                if tostring(rule.lhs) == nd.sym
                    and rule.rhs:len() == 0 then
                    return nil, ""   -- ok, contributes nothing
                end
            end
            return "leaf '" .. nd.sym .. "' is a variable without a "
                .. "λ-rule — expand it or write it as "
                .. nd.sym .. "(λ)"
        end
        return nil, nd.sym == "λ" and "" or nd.sym
    end
    if not vars[nd.sym] then
        return "node '" .. nd.sym .. "' has children but is not a "
            .. "variable"
    end
    local rhs = {}
    local yield = {}
    for _, ch in ipairs(kids) do
        local err, y = check_tree_node(ch, grammar, vars, syms)
        if err then return err end
        if ch.sym ~= "λ" then rhs[#rhs + 1] = ch.sym end
        yield[#yield + 1] = y
    end
    local rhs_s = table.concat(rhs)
    local found = false
    for rule, _ in pairs(grammar:get_rules()) do
        if tostring(rule.lhs) == nd.sym
            and ((rule.rhs:len() == 0 and rhs_s == "")
                 or tostring(rule.rhs) == rhs_s) then
            found = true; break
        end
    end
    if not found then
        return "node '" .. nd.sym .. "': the children '"
            .. (rhs_s ~= "" and rhs_s or "λ") .. "' are not the "
            .. "right-hand side of a rule " .. nd.sym .. " → …"
    end
    return nil, table.concat(yield)
end

-- part: {grammar=text, target=word, count=N, distinct=bool}
-- input: list of textarea strings (one per tree)
local function check_one_tree(part, text)
    text = text or ""
    if not text:match("%S") then
        return fail("enter the tree in bracket notation, e.g. "
            .. "S(a b S(c))", "empty")
    end
    local pr = grammar_of(part.grammar or "")
    local grammar = pr.g
    local t, err = parse_tree(text)
    if not t then return fail("tree: " .. err, "parse") end
    local start = tostring(grammar:get_start_variable())
    if t.sym ~= start then
        return fail("the root must be the start variable " .. start)
    end
    local vars, syms = grammar:get_variables(), grammar:get_symbols()
    local cerr, yield = check_tree_node(t, grammar, vars, syms)
    if cerr then return fail(cerr) end
    local target = (part.target or ""):gsub("%s", "")
    if yield ~= target then
        return fail("the leaves spell '" .. (yield ~= "" and yield
            or "λ") .. "', not '" .. target .. "'")
    end
    return { ok = true }
end

function M.check_tree(part, texts)
    if type(texts) == "string" then texts = { texts } end
    texts = texts or {}
    local want = part.count or 1
    local norm = {}
    for d = 1, want do
        local r = check_one_tree(part, texts[d] or "")
        if not r.ok then
            if want > 1 and r.msg then
                r.msg = "tree #" .. d .. ": " .. r.msg
            end
            return r
        end
        norm[d] = (texts[d] or ""):gsub("%s", "")
    end
    if part.distinct and want >= 2 then
        local same = true
        for d = 2, want do
            if norm[d] ~= norm[1] then same = false end
        end
        if same then
            return fail("the two trees are identical — that does "
                .. "not show ambiguity")
        end
    end
    return { ok = true }
end

-- ---------- set-notation pattern part ----------
--
-- The student describes L(G) as a block pattern over declared
-- variables, e.g.   (ab)^n c^m d^m c^n   with vars n,m.
-- Verification is two-sided and sampled, reported honestly:
--   ⊆: every grammar word up to length N must match the pattern
--   ⊇: every pattern instance (small grid) must be in L(G)

local function parse_pat_exp(s, vars)
    s = s:gsub("%s", "")
    local c = tonumber(s)
    if c then return { c = c } end
    local v, add = s:match("^(%a)%+(%d+)$")
    if not v then v, add = s:match("^(%a)$"), 0 end
    if v and vars[v] then
        return { var = v, add = tonumber(add) or 0 }
    end
    return nil
end

function M.parse_language_pattern(s, vars)
    -- segments: word^exp  or  bare word;  exponent braces () or {}
    local blocks, i, n = {}, 1, #s
    while i <= n do
        local c = s:sub(i, i)
        if c:match("%s") then i = i + 1
        else
            local word
            if c == "(" then
                local j = s:find(")", i + 1, true)
                if not j then return nil, "missing ')'" end
                word, i = s:sub(i + 1, j - 1), j + 1
            else
                word, i = c, i + 1
            end
            local exp = { c = 1 }
            if s:sub(i, i) == "^" then
                i = i + 1
                local open = s:sub(i, i)
                local body
                if open == "{" or open == "(" then
                    local close = open == "{" and "}" or ")"
                    local j = s:find(close, i + 1, true)
                    if not j then return nil, "missing '" .. close
                        .. "'" end
                    body, i = s:sub(i + 1, j - 1), j + 1
                else
                    -- bare exponent: a number or ONE variable letter
                    -- (longer exponents need braces — the next letter
                    -- would otherwise be ambiguous with a block start)
                    body = s:match("^%d+", i) or s:match("^%a", i)
                    if not body then
                        return nil, "missing exponent after '^'"
                    end
                    i = i + #body
                end
                exp = parse_pat_exp(body, vars)
                if not exp then
                    return nil, "bad exponent '" .. body .. "' (a "
                        .. "variable or a constant)"
                end
            end
            blocks[#blocks + 1] = { word = word, exp = exp }
        end
    end
    if #blocks == 0 then return nil, "empty pattern" end
    return blocks
end

-- does the word have a segmentation matching the blocks?
-- bound maps var → value already fixed; min[v] is the domain bound
local function pat_match(word, blocks, bi, pos, bound, min)
    if bi > #blocks then return pos > #word end
    local b = blocks[bi]
    local lw = #b.word
    local counts
    if b.exp.c then
        counts = { b.exp.c }
    else
        counts = {}
        if bound[b.exp.var] then
            counts[1] = bound[b.exp.var] + (b.exp.add or 0)
        else
            -- try every feasible repetition count
            local max = math.floor((#word - pos + 1) / lw)
            for t = 0, max do counts[#counts + 1] = t end
        end
    end
    for _, t in ipairs(counts) do
        if t >= 0 and pos + t * lw - 1 <= #word
            and word:sub(pos, pos + t * lw - 1) == b.word:rep(t) then
            local nb = bound
            if b.exp.var and not bound[b.exp.var] then
                local v = t - (b.exp.add or 0)
                if v >= (min and min[b.exp.var] or 0) then
                    nb = {}
                    for k, x in pairs(bound) do nb[k] = x end
                    nb[b.exp.var] = v
                else
                    nb = nil
                end
            end
            if nb and pat_match(word, blocks, bi + 1,
                    pos + t * lw, nb, min) then
                return true
            end
        end
    end
    return false
end

local function pat_instances(blocks, varlist, bound, i, maxlen,
                             out, min)
    if i > #varlist then
        -- emit the instantiated word
        local parts = {}
        for _, b in ipairs(blocks) do
            local t = b.exp.c or (bound[b.exp.var] + (b.exp.add or 0))
            parts[#parts + 1] = b.word:rep(t)
        end
        local w = table.concat(parts)
        if #w <= maxlen then out[#out + 1] = w end
        return
    end
    local v = varlist[i]
    for val = (min and min[v] or 0), 5 do
        bound[v] = val
        pat_instances(blocks, varlist, bound, i + 1, maxlen,
                      out, min)
    end
    bound[v] = nil
end

-- "n≥0, m>0" / "n>=0" guard tail -> per-variable lower bounds:
--   v>k  means  v ≥ k+1 ;  v≥k / v>=k  mean  v ≥ k
local function parse_guards(s, vars)
    local min = {}
    for cond in (s or ""):gmatch("[^,;]+") do
        local v, op, k =
            cond:match("^%s*(%a)%s*([≥>=]*)%s*(%d+)")
        if not v or not vars[v] then return nil end
        k = tonumber(k)
        if op == ">" then k = k + 1 end
        min[v] = k
    end
    return min
end

-- part: {grammar=text, vars="n,m", min={n=0,m=1}, maxlen=N}
function M.check_pattern(part, text)
    text = text or ""
    if not text:match("%S") then
        return fail("describe L(G) as a block pattern, e.g. "
            .. "(ab)^n c^m d^m c^n", "empty")
    end
    local vars = {}
    local varlist = {}
    local src_vars = type(part.vars) == "table"
        and table.concat(part.vars, ",") or (part.vars or "n,m")
    for v in src_vars:gmatch("[%a_]+") do
        vars[v] = true; varlist[#varlist + 1] = v
    end
    -- optional domain guards after '|':  (ab)^n c^m d^m c^n | m>0
    local pat_text, guard_text = text:match("^(.-)|(.*)$")
    if not pat_text then pat_text = text end
    local min = parse_guards(guard_text or "", vars)
    if guard_text and not min then
        return fail("could not read the domain guards — write e.g. "
            .. "| n≥0, m>0", "parse")
    end
    local blocks, perr = M.parse_language_pattern(pat_text, vars)
    if not blocks then return fail(perr, "parse") end
    local grammar = grammar_of(part.grammar or "").g
    local maxlen = part.maxlen or 22
    -- ⊆: grammar words up to maxlen must match the pattern
    local words = automata.grammar_enumerate_words(
        grammar, maxlen, { max_words = 4000 }) or {}
    for ws, _ in pairs(words) do
        if #ws <= maxlen
            and not pat_match(ws, blocks, 1, 1, {}, min) then
            return fail("'" .. (ws ~= "" and ws or "λ")
                .. "' ∈ L(G) does not match your pattern", "mismatch")
        end
    end
    -- ⊇: every small instance must be derivable
    local insts = {}
    pat_instances(blocks, varlist, {}, 1, maxlen, insts, min)
    local start_sym = tostring(grammar:get_start_variable())
    local function derives_lambda()
        for rule, _ in pairs(grammar:get_rules()) do
            if tostring(rule.lhs) == start_sym
                and #rule.rhs == 0 then
                return true
            end
        end
        return false
    end
    for _, w in ipairs(insts) do
        local member
        if w == "" then
            member = derives_lambda()
        else
            member = automata.grammar_contains_word(
                w, grammar, { max_iter = 4000 })
        end
        if not member then
            return fail("'" .. (w ~= "" and w or "λ")
                .. "' matches your pattern but ∉ L(G)", "mismatch")
        end
    end
    return { ok = true,
             msg = "verified on all words of length ≤ " .. maxlen
                .. " in both directions" }
end

-- ---------- grammar normalisation (sheet 5) ----------
-- part.form decides the structural property:
--   "essentially_noncontracting"  only the start symbol may have λ
--   "no_chain"        no unit rules A → B
--   "terminating"     every variable derives a terminal word
--   "no_useless"      every variable is terminating AND reachable
--   "cnf"             Chomsky normal form
-- plus language equivalence to part.grammar_ref when given.

local function grammar_vars_reachable(g)
    -- variables that produce a terminal word (productive)
    local vars = g:get_variables()
    local term = {}
    local changed = true
    while changed do
        changed = false
        for rule, _ in pairs(g:get_rules()) do
            local lhs = tostring(rule.lhs)
            if not term[lhs] then
                local ok = true
                for i = 1, rule.rhs:len() do
                    local c = tostring(rule.rhs:get_char(i))
                    if vars[c] and not term[c] then
                        ok = false; break
                    end
                end
                if ok then term[lhs] = true; changed = true end
            end
        end
    end
    return term
end

local function grammar_vars_reached(g)
    -- variables reachable from the start symbol
    local reached = { [tostring(g:get_start_variable())] = true }
    local changed = true
    while changed do
        changed = false
        for rule, _ in pairs(g:get_rules()) do
            local lhs = tostring(rule.lhs)
            if reached[lhs] then
                for i = 1, rule.rhs:len() do
                    local c = tostring(rule.rhs:get_char(i))
                    if not reached[c] then
                        reached[c] = true; changed = true
                    end
                end
            end
        end
    end
    return reached
end

local FORM_CHECKS = {
    essentially_noncontracting = function(g)
        if automata.grammar_is_essentially_noncontracting(g) then
            return nil
        end
        return "not essentially noncontracting — only the (new) "
            .. "start symbol may have a λ-rule"
    end,
    no_chain = function(g)
        local vars = g:get_variables()
        for rule, _ in pairs(g:get_rules()) do
            if rule.rhs:len() == 1
                and vars[tostring(rule.rhs:get_char(1))] then
                return "chain rule "
                    .. tostring(rule.lhs) .. " → "
                    .. tostring(rule.rhs) .. " still present"
            end
        end
        return nil
    end,
    terminating = function(g)
        local term = grammar_vars_reachable(g)
        for v, _ in pairs(g:get_variables()) do
            if not term[v] then
                return "variable " .. v
                    .. " derives no terminal word (nonterminating)"
            end
        end
        return nil
    end,
    no_useless = function(g)
        local term = grammar_vars_reachable(g)
        local reached = grammar_vars_reached(g)
        for v, _ in pairs(g:get_variables()) do
            if not term[v] then
                return "variable " .. v
                    .. " derives no terminal word (nonterminating)"
            end
            if not reached[v] then
                return "variable " .. v
                    .. " is unreachable from the start symbol"
            end
        end
        return nil
    end,
    cnf = function(g)
        if automata.grammar_is_cnf(g) then return nil end
        return "not in Chomsky normal form — rules must be "
            .. "A → BC or A → a (plus S → λ)"
    end,
}

function M.check_normalise(part, text)
    local pr = grammar_of(text or "")
    local g = pr.g
    local any = false
    for _ in pairs(g:get_rules()) do any = true; break end
    if not any then return fail("no rules parsed", "parse") end
    local err = FORM_CHECKS[part.form](g)
    if err then return fail(err) end
    if part.grammar_ref then
        local ref = grammar_of(part.grammar_ref).g
        local res, cex_s, cex_r = automata.grammar_compare_languages(
            ref, g, { max_iter = 150000, deadline = os.clock() + 8 })
        if res == "=" then
            return { ok = true }
        end
        if res then
            local bits = {}
            if cex_s then bits[#bits + 1] = "'" .. (cex_s ~= ""
                and cex_s or "λ") .. "' ∈ L(G) but not derivable" end
            if cex_r then bits[#bits + 1] = "'" .. (cex_r ~= ""
                and cex_r or "λ") .. "' is derivable but ∉ L(G)" end
            return fail(table.concat(bits, ";  "), "mismatch")
        end
        return { ok = true,
                 msg = "the form is right; language equality could "
                    .. "not be fully verified — check by hand" }
    end
    return { ok = true }
end

-- ---------- CYK matrix (sheet 5) ----------
-- part: {grammar=text, word="acba"}
-- input: cells map "i,j" (i..j substring) -> student set text

local function cyk_table(word, g)
    local cnf = automata.grammar_to_cnf(g)
    local n = #word
    local at = {}
    for i = 1, n do
        at[i] = { [1] = {} }
        local term = cnf.terminals[word:sub(i, i)]
        if term then for v, _ in pairs(term) do at[i][1][v] = true end
        end
    end
    for len = 2, n do
        for i = 1, n - len + 1 do
            local cell = {}
            for k = 1, len - 1 do
                for b, _ in pairs(at[i][k] or {}) do
                    local by_c = cnf.pairs[b]
                    if by_c then
                        for c, _ in pairs(at[i + k][len - k] or {}) do
                            local prods = by_c[c]
                            if prods then
                                for a, _ in pairs(prods) do
                                    cell[a] = true
                                end
                            end
                        end
                    end
                end
            end
            at[i][len] = cell
        end
    end
    -- at[i][len] covers substring i..i+len-1; re-index to X_{i,j}
    local x = {}
    for i = 1, n do
        x[i] = {}
        for len = 1, n - i + 1 do
            x[i][i + len - 1] = at[i][len]
        end
    end
    return x, cnf
end

local function parse_set_text(text)
    -- "{S,E}", "S E", "S,E", "-", "∅" -> set, errmsg
    local s = (text or ""):gsub("%s", "")
    if s == "" or s == "-" or s == "∅" or s == "{}" then
        return {}
    end
    s = s:gsub("[{}]", "")
    local set = {}
    for v in s:gmatch("[^,;]+") do
        set[v] = true
    end
    return set
end

function M.check_cyk(part, cells)
    local pr = grammar_of(part.grammar or "")
    local word = part.word
    local x, cnf = cyk_table(word, pr.g)
    local n = #word
    local missing, wrong = 0, nil
    for i = 1, n do
        for j = i, n do
            local got = parse_set_text(cells and cells[i .. "," .. j])
            local want = x[i][j] or {}
            for v, _ in pairs(got) do
                if not want[v] then
                    return fail("X_{" .. i .. "," .. j .. "}: '"
                        .. v .. "' is not produced by CYK "
                        .. "(check the splits of '" .. word:sub(i, j)
                        .. "')", "mismatch")
                end
            end
            for v, _ in pairs(want) do
                if not got[v] then
                    if (cells and cells[i .. "," .. j] or "") == ""
                        then missing = missing + 1
                        else
                        wrong = "X_{" .. i .. "," .. j
                            .. "} should also contain '" .. v
                            .. "' (a split of '" .. word:sub(i, j)
                            .. "' is missing)"
                    end
                end
            end
        end
    end
    if wrong then return fail(wrong, "mismatch") end
    if missing > 0 then
        return fail(missing .. " cell(s) still empty "
            .. "(enter - or ∅ for an empty set)", "empty")
    end
    local start = tostring(cnf.start)
    local root = x[1][n] or {}
    return { ok = true,
             msg = "X_{1," .. n .. "} = {" .. table.concat(
                (function() local t = {}
                    for v in pairs(root) do t[#t+1] = v end
                    table.sort(t) return t end)(), ",")
                .. "}  →  " .. (root[start] and "the word IS in L(G)"
                    or "the word is NOT in L(G)") }
end

return M
