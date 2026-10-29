-- Formula AST utilities for logic/syntax.lua trees:
-- canonical rendering, free variables, atoms, substitution.
-- Everything operates on the plain JSON-compatible AST nodes the
-- parser produces ({type=..., pos={from,to}}).

local operators = require "logic.operators"

local formula = {}

-- ---------------------------------------------------------------------
-- rendering

local OP_SYM = {}
for _, op in ipairs(operators.connectives) do
    OP_SYM[op.key] = op.default_symbol
end

local function render_term(t)
    if t.type == "var" or t.type == "const" or t.type == "name" then
        return t.name
    end
    local parts = {}
    for i, a in ipairs(t.args) do parts[i] = render_term(a) end
    return t.name .. "(" .. table.concat(parts, ",") .. ")"
end

-- minimal parenthesisation: a binary op child is parenthesised when it
-- is weaker-binding than its parent, or is the right child of a
-- non-associative-op parent at equal precedence, etc.  We keep it
-- simple and faithful: parenthesise every op/quant child unless the
-- child is atomic.  The canonical render is therefore fully
-- parenthesised except for prefix chains and quantifiers.
local function render(f)
    if f.type == "true" then return "⊤" end
    if f.type == "false" then return "⊥" end
    if f.type == "atom" then
        if #f.args == 0 then return f.name end
        local parts = {}
        for i, a in ipairs(f.args) do parts[i] = render_term(a) end
        return f.name .. "(" .. table.concat(parts, ",") .. ")"
    end
    if f.type == "quant" then
        local vs = {}
        for i, v in ipairs(f.vars) do vs[i] = v.name end
        local q = f.quant == "forall" and "∀" or "∃"
        return q .. table.concat(vs, ",") .. "." .. render(f.body)
    end
    -- op
    local sym = OP_SYM[f.op] or f.op
    if f.op == "not" then
        local inner = render(f.args[1])
        local a = f.args[1]
        if a.type == "quant" or (a.type == "op" and a.op ~= "not") then
            inner = "(" .. inner .. ")"
        end
        return sym .. inner
    end
    local l, r = f.args[1], f.args[2]
    local ls, rs = render(l), render(r)
    if l.type == "op" or l.type == "quant" then ls = "(" .. ls .. ")" end
    if r.type == "op" or r.type == "quant" then rs = "(" .. rs .. ")" end
    return ls .. sym .. rs
end

formula.render = render
formula.render_term = render_term

-- ---------------------------------------------------------------------
-- free variables

local function free_vars(f)
    local bound, out, seen = {}, {}, {}
    local function tw(t)
        if t.type == "var" then
            if not bound[t.name] and not seen[t.name] then
                seen[t.name] = true
                out[#out + 1] = t.name
            end
        elseif t.type == "func" then
            for _, a in ipairs(t.args) do tw(a) end
        end
    end
    local function w(n)
        if n.type == "atom" then
            for _, a in ipairs(n.args) do tw(a) end
        elseif n.type == "op" then
            for _, a in ipairs(n.args) do w(a) end
        elseif n.type == "quant" then
            for _, v in ipairs(n.vars) do
                bound[v.name] = (bound[v.name] or 0) + 1
            end
            w(n.body)
            for _, v in ipairs(n.vars) do
                bound[v.name] = bound[v.name] - 1
                if bound[v.name] == 0 then bound[v.name] = nil end
            end
        end
    end
    w(f)
    return out
end

formula.free_vars = free_vars
formula.closed = function(f) return #free_vars(f) == 0 end

-- ---------------------------------------------------------------------
-- atoms / vocabulary

-- atom occurrences (for truth-table skeletons): {name,args?} list,
-- duplicates removed by canonical key
local function atoms(f)
    local out, seen = {}, {}
    local function w(n)
        if n.type == "atom" then
            local key = n.name
            if #n.args > 0 then
                local ps = {}
                for i, a in ipairs(n.args) do
                    ps[i] = render_term(a)
                end
                key = n.name .. "(" .. table.concat(ps, ",") .. ")"
            end
            if not seen[key] then
                seen[key] = true
                out[#out + 1] = n
            end
        elseif n.type == "op" then
            for _, a in ipairs(n.args) do w(a) end
        elseif n.type == "quant" then
            w(n.body)
        end
    end
    w(f)
    return out
end

formula.atoms = atoms

-- ---------------------------------------------------------------------
-- substitution
--
-- subst: {varname -> term-ast}
-- subst_term / subst_formula capture-avoid: when a quantifier binds a
-- variable occurring in any replacement term's free vars, the bound
-- variable is renamed to a fresh name first.

local function term_free_vars(t, out)
    if t.type == "var" then
        out[t.name] = true
    elseif t.type == "func" then
        for _, a in ipairs(t.args) do term_free_vars(a, out) end
    end
    return out
end

local function subst_term(t, subst)
    if t.type == "var" then
        local r = subst[t.name]
        return r and r or t
    elseif t.type == "func" then
        local args = {}
        for i, a in ipairs(t.args) do
            args[i] = subst_term(a, subst)
        end
        return {type = "func", name = t.name, args = args, pos = t.pos}
    end
    return t
end

local function fresh_name(taken, base)
    local i = 0
    local cand = base
    while taken[cand] do
        i = i + 1
        cand = base .. i
    end
    return cand
end

local subst_formula

-- rename a bound variable throughout a formula (alpha conversion)
local function rename_bound(f, old, new)
    if f.type == "atom" then
        local args = {}
        for i, a in ipairs(f.args) do
            args[i] = subst_term(a, {[old] = {type = "var", name = new}})
        end
        return {type = "atom", name = f.name, args = args, pos = f.pos}
    elseif f.type == "op" then
        local args = {}
        for i, a in ipairs(f.args) do
            args[i] = rename_bound(a, old, new)
        end
        return {type = "op", op = f.op, args = args, pos = f.pos}
    elseif f.type == "quant" then
        local vars = {}
        for i, v in ipairs(f.vars) do
            vars[i] = {name = v.name == old and new or v.name,
                       pos = v.pos}
        end
        return {type = "quant", quant = f.quant, vars = vars,
                body = rename_bound(f.body, old, new), pos = f.pos}
    end
    return f
end

subst_formula = function(f, subst)
    if f.type == "atom" then
        local args = {}
        for i, a in ipairs(f.args) do
            args[i] = subst_term(a, subst)
        end
        return {type = "atom", name = f.name, args = args, pos = f.pos}
    elseif f.type == "op" then
        local args = {}
        for i, a in ipairs(f.args) do
            args[i] = subst_formula(a, subst)
        end
        return {type = "op", op = f.op, args = args, pos = f.pos}
    elseif f.type == "quant" then
        -- restrict subst to non-bound names
        local eff = {}
        for k, v in pairs(subst) do eff[k] = v end
        for _, v in ipairs(f.vars) do eff[v.name] = nil end
        -- capture check: any bound var that appears free in a
        -- replacement term must be renamed first
        local repl_free = {}
        for _, t in pairs(eff) do term_free_vars(t, repl_free) end
        local body = f.body
        local vars = {}
        for i, v in ipairs(f.vars) do vars[i] = v.name end
        local taken = {}
        for k in pairs(eff) do taken[k] = true end
        for k in pairs(repl_free) do taken[k] = true end
        for _, v in ipairs(f.vars) do taken[v.name] = true end
        for i, v in ipairs(vars) do
            if repl_free[v] then
                local new = fresh_name(taken, v)
                taken[new] = true
                body = rename_bound(body, v, new)
                vars[i] = new
            end
        end
        local vnodes = {}
        for i, n in ipairs(vars) do
            vnodes[i] = {name = n}
        end
        return {type = "quant", quant = f.quant, vars = vnodes,
                body = subst_formula(body, eff), pos = f.pos}
    end
    return f
end

formula.subst_term = subst_term
formula.subst_formula = subst_formula
formula.rename_bound = rename_bound
formula.fresh_name = fresh_name

-- ---------------------------------------------------------------------
-- structural equality (positions ignored)

local function terms_equal(a, b)
    if a.type ~= b.type then return false end
    if a.type == "func" then
        if a.name ~= b.name or #a.args ~= #b.args then return false end
        for i = 1, #a.args do
            if not terms_equal(a.args[i], b.args[i]) then
                return false
            end
        end
        return true
    end
    return a.name == b.name
end

local function equal(a, b)
    if a.type ~= b.type then return false end
    if a.type == "atom" then
        if a.name ~= b.name or #a.args ~= #b.args then return false end
        for i = 1, #a.args do
            if not terms_equal(a.args[i], b.args[i]) then
                return false
            end
        end
        return true
    elseif a.type == "op" then
        if a.op ~= b.op or #a.args ~= #b.args then return false end
        for i = 1, #a.args do
            if not equal(a.args[i], b.args[i]) then return false end
        end
        return true
    elseif a.type == "quant" then
        if a.quant ~= b.quant or #a.vars ~= #b.vars then return false end
        for i = 1, #a.vars do
            if a.vars[i].name ~= b.vars[i].name then return false end
        end
        return equal(a.body, b.body)
    end
    return true   -- true/false
end

formula.equal = equal
formula.terms_equal = terms_equal

return formula
