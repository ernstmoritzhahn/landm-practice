-- Classical-logic formula parser (propositional + predicate),
-- Advanced Logic course / Ben-Ari notation.
--
-- Generic precedence-climbing LPeg grammar built from
-- logic.operators.  Produces plain JSON-compatible ASTs with byte
-- positions; errors use lib.parsing_context farthest-failure tracking
-- ("expected … at position n").  The label/journal hooks the BayesL
-- suggestion engine consumes (ctx:Label/Suggest/Note) are already the
-- mechanism used here for error reporting, so offer-lists can be added
-- on the same positions later.
--
-- AST shapes (every node has pos={from,to}, 1-based byte offsets):
--   {type="true"|"false"}
--   {type="atom",  name="p", args={term,...}}   -- args={} = prop atom
--   {type="op",    op="not"|"and"|"or"|"nand"|"nor"|"imp"|"revimp"|
--                     "iff"|"xor", args={f[,f]}}
--   {type="quant", quant="forall"|"exists",
--                  vars={{name="x",pos=...},...}, body=f}
-- term:
--   {type="const", name="a"} | {type="var", name="x"}
--   {type="func",  name="f", args={term,...}}
--
-- Identifier classification (post-parse scope walk): a bare term
-- inside a quantifier's scope with the bound name is a var; otherwise
-- a bare term whose initial is in var_initials (default "uvwxyz")
-- is a (free) var; anything else is a const.  Functor positions are
-- always function symbols.

local lpeg = require "lpeg"
local parsing_context = require "lib.parsing_context"
local lpeg_util = require "lib.lpeg_util"
local operators = require "logic.operators"

local P, S, V, R = lpeg.P, lpeg.S, lpeg.V, lpeg.R
local C, Ct, Cp, Cmt, Cc = lpeg.C, lpeg.Ct, lpeg.Cp, lpeg.Cmt, lpeg.Cc

local Space = S(" \t\n")^0
local Open  = P("(") * Space
local Close = P(")") * Space
local Comma = P(",") * Space
local Dot   = P(".") * Space

-- expect(label): farthest-failure annotation that also tells LPeg's
-- nullability analysis the position consumes input (a bare Label is a
-- Cmt over P(true) and would make recursive rules look left-recursive).
local function expect(label)
    return parsing_context.Label(label) * P(false)
end

local ident_char = R("az", "AZ", "09") + S("_'")
local Ident_raw  = R("az", "AZ") * ident_char^0
local boundary   = -ident_char            -- lookahead: ident ends here

-- reserved words never parse as identifiers: word connectives,
-- quantifier words, boolean constants
local reserved = P(false)
for _, group in ipairs({operators.connectives, operators.quantifiers,
                        operators.constants}) do
    for _, e in ipairs(group) do
        for _, w in ipairs(e.word_symbols or {}) do
            reserved = reserved + P(w) * boundary
        end
    end
end

local Ident = -reserved * Ident_raw

-- token builders ------------------------------------------------------

-- fixed symbol token (unicode/ascii, verbatim match)
local function symtok(s)
    return P(s) * Space
end

-- word token: needs an identifier boundary after it
local function wordtok(w)
    return P(w) * boundary * Space
end

-- ordered alternation over an op's symbol+word forms, producing the
-- op entry itself; word symbols last (they need the boundary check
-- anyway and fixed symbols are cheaper to try).
local function op_pattern(op)
    local patt = P(false)
    for _, s in ipairs(op.symbols or {}) do
        patt = patt + symtok(s)
    end
    for _, w in ipairs(op.word_symbols or {}) do
        patt = patt + wordtok(w)
    end
    return patt / function() return op end
end

local function ops_pattern(ops)
    local patt = P(false)
    for _, op in ipairs(ops) do
        patt = patt + op_pattern(op)
    end
    return patt
end

-- AST constructors ----------------------------------------------------

local function mkpos(f, t)
    return {from = f, to = t}
end

local function node(type, f, t, fields)
    local n = {type = type, pos = mkpos(f, t)}
    if fields then
        for k, v in pairs(fields) do n[k] = v end
    end
    return n
end

-- grammar -------------------------------------------------------------

local syntax = {}

-- Precedence levels are sorted tightest-first internally; the formula
-- rule is the loosest level.  All binary connectives fold to the right
-- (matches the operator table and the usual reading of p->q->r).
local function build_grammar()
    -- group connectives by precedence
    local by_prec, precs = {}, {}
    for _, op in ipairs(operators.connectives) do
        local p = op.precedence
        if not by_prec[p] then
            by_prec[p] = {}
            precs[#precs + 1] = p
        end
        by_prec[p][#by_prec[p] + 1] = op
    end
    table.sort(precs)            -- ascending: level_1 loosest, level_n tightest
    local top = precs[#precs]    -- tightest precedence number

    local grammar = {"formula"}

    grammar.formula = V("level_" .. precs[1])

    -- base operand: constants, quantifiers, atoms, parenthesised.
    -- The trailing expect-labels are the operand-start vocabulary:
    -- at a farthest-failure position they ARE the valid continuations
    -- (suggestions map each label to insertable tokens).
    grammar.base =
        P(false)
        + V("boolconst")
        + V("quant")
        + V("atom")
        + Open * V("formula")
          * (Close + expect("')'"))
        + expect("identifier")
        + expect("'¬'")
        + expect("quantifier")
        + expect("constant")
        + expect("'('")

    -- boolean constants
    do
        local patt = P(false)
        for _, c in ipairs(operators.constants) do
            local cp = P(false)
            for _, s in ipairs(c.symbols) do
                cp = cp + symtok(s)
            end
            for _, w in ipairs(c.word_symbols or {}) do
                cp = cp + wordtok(w)
            end
            patt = patt + (Cp() * cp * Cp()
                / function(f, t) return node(c.name, f, t) end)
        end
        grammar.boolconst = patt
    end

    -- quantifier: (∀|∃) var (, var)* . formula
    do
        local qsym = P(false)
        for _, q in ipairs(operators.quantifiers) do
            qsym = qsym + (op_pattern(q)
                / function() return q.name end)
        end
        local varname = (Cp() * C(Ident) * Cp() * Space
            / function(f, n, t)
                return {name = n, pos = mkpos(f, t)}
            end)
        -- ',' only expected when no comma was just consumed; a
        -- 'variable' expectation marks the position after it.
        local varlist = Ct(varname
            * ((Comma + expect("','") + P(true))
               * (varname + expect("variable")))^0)
        grammar.quant =
            Cp() * qsym * Space
            * (varlist + expect("variable"))
            * (Dot + expect("'.'"))
            * V("formula")
            * Cp()
            / function(f, quant, vars, body, t)
                return node("quant", f, t,
                            {quant = quant, vars = vars, body = body})
            end
    end

    -- atom / term identifiers
    do
        -- term argument list
        grammar.termlist = V("term")
            * (Comma * (V("term") + expect("term")))^0
            / function(first, ...)
                local args = {first}
                for _, a in ipairs({...}) do args[#args + 1] = a end
                return args
            end
        grammar.term =
            P(false)
            + (Cp() * C(Ident) * Space
               * Open
               * (V("termlist") + Cc({}))
               * (Close + expect("')'"))
               * Cp()
               / function(f, name, args, t)
                   return node("func", f, t, {name = name, args = args})
               end)
            + (Cp() * C(Ident) * Cp() * Space
               / function(f, name, t)
                   return node("name", f, t, {name = name})
               end)
            + expect("term")

        grammar.atom =
            P(false)
            + (Cp() * C(Ident) * Space
               * Open
               * (V("termlist") + Cc({}))
               * (Close + expect("')'"))
               * Cp()
               / function(f, name, args, t)
                   return node("atom", f, t, {name = name, args = args})
               end)
            + (Cp() * C(Ident) * Cp() * Space
               / function(f, name, t)
                   return node("atom", f, t, {name = name, args = {}})
               end)
    end

    -- precedence levels, tightest last in the chain
    for i = #precs, 1, -1 do
        local p = precs[i]
        local level_name = "level_" .. p
        local ops = by_prec[p]
        local prefix_ops, infix_ops = {}, {}
        for _, op in ipairs(ops) do
            if op.notation == "prefix" then
                prefix_ops[#prefix_ops + 1] = op
            else
                infix_ops[#infix_ops + 1] = op
            end
        end
        -- operand of this level: the tighter level, or base for the
        -- tightest level
        local operand
        if p == top then
            operand = V("base")
        else
            operand = V("level_" .. precs[i + 1])
        end
        local patt
        if #prefix_ops > 0 then
            -- chain of prefix ops then operand
            local pref = P(false)
            for _, op in ipairs(prefix_ops) do
                pref = pref + (Cp() * op_pattern(op)
                    / function(f, o) return f, o end)
            end
            patt = Ct((pref)^0 * operand) / function(parts)
                local inner = parts[#parts]
                for j = #parts - 2, 1, -2 do
                    local f, op = parts[j], parts[j + 1]
                    inner = node("op", f, inner.pos.to,
                                 {op = op.key, args = {inner}})
                end
                return inner
            end
        else
            -- infix level, right associative: operand (op level)?
            -- the trailing Label records a "connective or ')'"
            -- expectation at operator position when no op matches.
            local opp = ops_pattern(infix_ops)
            patt = operand * (Cp() * (opp
                + expect("connective"))
                * V(level_name) * Cp())^-1
                / function(left, f, op, right, t)
                    if not op then return left end
                    return node("op", left.pos.from, t,
                                {op = op.key, args = {left, right}})
                end
        end
        grammar[level_name] = patt
    end

    return P(grammar)
end

local formula_pattern = build_grammar()

-- term parser alone (for tableau gamma-terms etc.)
local term_pattern
do
    local g = {"term"}
    g.termlist = nil
    term_pattern = P{
        [1] = "term",
        term = P(false)
            + (Cp() * C(Ident) * Space
               * Open
               * (V("term") * (Comma * V("term"))^0
                  / function(first, ...)
                      local a = {first}
                      for _, x in ipairs({...}) do a[#a + 1] = x end
                      return a
                  end)
               * (Close + expect("')'"))
               * Cp()
               / function(f, name, args, t)
                   return node("func", f, t, {name = name, args = args})
               end)
            + (Cp() * C(Ident) * Cp() * Space
               / function(f, name, t)
                   return node("name", f, t, {name = name})
               end)
            + expect("term")
    }
end

-- post-pass: classify bare names as var/const by scope + convention,
-- collect free variables, check name/arity consistency.

local VAR_INITIALS = {u = true, v = true, w = true,
                      x = true, y = true, z = true}

local function classify_var(name, var_initials)
    return var_initials[name:sub(1, 1)] == true
end

local function post_process(ast, opts)
    local var_initials = (opts and opts.var_initials) or VAR_INITIALS
    local bound = {}          -- name -> count
    local free = {}           -- name -> pos (first free occurrence)
    local free_order = {}
    local roles = {}          -- name -> {atom_arity=?, func_arity=?}
    local errors = {}

    local function note_role(name, kind, arity, pos)
        local r = roles[name]
        if not r then
            r = {}
            roles[name] = r
        end
        local key = kind .. "_arity"
        if r[key] == nil then
            r[key] = arity
        elseif r[key] ~= arity then
            errors[#errors + 1] = {
                pos = pos,
                message = string.format(
                    "%s used with arity %d here but arity %d elsewhere",
                    name, arity, r[key]),
            }
        end
        if kind == "atom" and r.func_arity ~= nil
            or kind == "func" and r.atom_arity ~= nil then
            errors[#errors + 1] = {
                pos = pos,
                message = name .. " used both as predicate and function",
            }
        end
    end

    local function walk_term(t)
        if t.type == "name" then
            if bound[t.name] then
                t.type = "var"
            elseif classify_var(t.name, var_initials) then
                t.type = "var"
                if not free[t.name] then
                    free[t.name] = t.pos.from
                    free_order[#free_order + 1] = t.name
                end
            else
                t.type = "const"
            end
        else
            -- func
            note_role(t.name, "func", #t.args, t.pos)
            if bound[t.name] then
                errors[#errors + 1] = {
                    pos = t.pos,
                    message = t.name ..
                        " is a bound variable, cannot be a function",
                }
            end
            for _, a in ipairs(t.args) do walk_term(a) end
        end
    end

    local function walk(f)
        if f.type == "atom" then
            note_role(f.name, "atom", #f.args, f.pos)
            for _, a in ipairs(f.args) do walk_term(a) end
        elseif f.type == "op" then
            for _, a in ipairs(f.args) do walk(a) end
        elseif f.type == "quant" then
            for _, v in ipairs(f.vars) do
                bound[v.name] = (bound[v.name] or 0) + 1
            end
            walk(f.body)
            for _, v in ipairs(f.vars) do
                bound[v.name] = bound[v.name] - 1
                if bound[v.name] == 0 then bound[v.name] = nil end
            end
        end
    end
    walk(ast)

    return errors, free_order, roles
end

-- error reporting ------------------------------------------------------

local function format_expected(expected)
    if not expected or #expected == 0 then
        return "unexpected input"
    end
    if #expected == 1 then
        return "expected " .. expected[1]
    end
    return "expected " .. table.concat(expected, " or ")
end

local function make_error(input, pos, expected)
    local line, col = nil, nil
    if pos then
        local util = require "lib.util"
        line, col = util.index_to_line_and_column(input, pos)
    end
    return {
        pos = pos,
        line = line,
        column = col,
        expected = expected,
        message = format_expected(expected) ..
            (pos and string.format(" at position %d", pos) or ""),
    }
end

-- public API -----------------------------------------------------------

--- parse(input, opts) -> ast | nil, err | nil, info
--- opts.var_initials: set of initials classified as free variables
--- On success also returns info = {free={...}, roles={...}, errors={..}}
local top_pattern = Space * formula_pattern * Space * Cp()

function syntax.parse(input, opts)
    local prev = parsing_context.get_current()
    local ctx = parsing_context(input)
    parsing_context.set_current(ctx)
    local ast, endpos = lpeg.match(top_pattern, input)
    parsing_context.set_current(prev)
    if ast == nil or endpos <= #input then
        local pos = ctx:get_last_position()
        local expected = ctx:get_expected()
        if endpos and endpos > (pos or 0) then
            pos = endpos
            expected = nil
        end
        return nil, make_error(input, pos, expected)
    end
    local errors, free, roles = post_process(ast, opts)
    if #errors > 0 then
        local e = errors[1]
        local err = make_error(input, e.pos.from, nil)
        err.message = e.message ..
            string.format(" at position %d", e.pos.from)
        return nil, err
    end
    return ast, nil, {free = free, roles = roles}
end

-- context-sensitive suggestions -------------------------------------
--
-- suggest(prefix) parses the text before the caret and reads the
-- farthest-failure expectation set — that set IS the continuation
-- vocabulary (successful parses still register the infix "connective"
-- probe at end-of-input).  Each expectation label maps to insertable
-- tokens; `back` is the number of characters the caret moves back
-- after insertion (lands inside () for the (…)-style offers).

local SUGGEST_TOKENS = {
    ["identifier"]  = {{"p"}, {"p()", back = 1}},
    ["'¬'"]         = {{"¬"}},
    ["'('"]         = {{"()", back = 1}},
    ["quantifier"]  = {{"∀"}, {"∃"}},
    ["constant"]    = {{"⊤"}, {"⊥"}},
    ["variable"]    = {{"x"}, {"y"}},
    ["term"]        = {{"a"}, {"x"}, {"f()", back = 1}},
    ["')'"]         = {{")"}},
    ["','"]         = {{","}},
    ["'.'"]         = {{"."}},
}
do
    local order = {"and", "or", "imp", "iff", "xor", "nand", "nor",
                   "revimp"}
    local list = {}
    for _, key in ipairs(order) do
        local op = operators.by_key[key]
        list[#list + 1] = {op.default_symbol}
    end
    SUGGEST_TOKENS["connective"] = list
end

--- suggest(prefix) -> {{ins=string, back=int?}, ...}
--- prefix: input text up to the caret (byte string).
function syntax.suggest(prefix)
    local prev = parsing_context.get_current()
    local ctx = parsing_context(prefix)
    parsing_context.set_current(ctx)
    lpeg.match(top_pattern, prefix)
    local expected = ctx:get_expected() or {}
    parsing_context.set_current(prev)
    local seen, out = {}, {}
    for _, label in ipairs(expected) do
        for _, t in ipairs(SUGGEST_TOKENS[label] or {}) do
            if not seen[t[1]] then
                seen[t[1]] = true
                out[#out + 1] = {ins = t[1], back = t.back}
            end
        end
    end
    return out
end

--- parse a standalone term (gamma-rule inputs etc.)
function syntax.parse_term(input, opts)
    local prev = parsing_context.get_current()
    local ctx = parsing_context(input)
    parsing_context.set_current(ctx)
    local pat = Space * term_pattern * Space * Cp()
    local result, endpos = lpeg.match(pat, input)
    if result == nil or endpos <= #input then
        local pos = ctx:get_last_position()
        parsing_context.set_current(prev)
        return nil, make_error(input, pos, ctx:get_expected())
    end
    parsing_context.set_current(prev)
    -- classify: no bound context -> convention only
    local vi = (opts and opts.var_initials) or VAR_INITIALS
    local function fix(t)
        if t.type == "name" then
            t.type = classify_var(t.name, vi) and "var" or "const"
        else
            for _, a in ipairs(t.args) do fix(a) end
        end
    end
    fix(result)
    return result
end

syntax.operators = operators
syntax.VAR_INITIALS = VAR_INITIALS

return syntax
