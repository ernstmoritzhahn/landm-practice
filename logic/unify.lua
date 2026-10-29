-- Terms, substitutions and unification for predicate logic.
-- Substitution: {varname -> term-ast}.  Works on the term nodes from
-- logic/syntax (var/const/func).

local formula = require "logic.formula"

local unify = {}

local subst_term = formula.subst_term

-- apply a substitution to a literal/atom (keeps negation separate —
-- literals are atoms possibly wrapped in op.not)
local function subst_expr(e, subst)
    if e.type == "atom" then
        local args = {}
        for i, a in ipairs(e.args) do args[i] = subst_term(a, subst) end
        return {type = "atom", name = e.name, args = args, pos = e.pos}
    elseif e.type == "op" and e.op == "not" then
        return {type = "op", op = "not",
                args = {subst_expr(e.args[1], subst)}, pos = e.pos}
    end
    return formula.subst_formula(e, subst)
end

unify.subst_term = subst_term
unify.subst_expr = subst_expr

-- substitution composition: s2∘s1 — apply s1 first, then s2
local function compose(s1, s2)
    local out = {}
    for v, t in pairs(s1) do
        out[v] = subst_term(t, s2)
    end
    for v, t in pairs(s2) do
        if s1[v] == nil then
            out[v] = t
        end
    end
    -- drop identity bindings
    for v, t in pairs(out) do
        if t.type == "var" and t.name == v then
            out[v] = nil
        end
    end
    return out
end

unify.compose = compose

-- occurs check
local function occurs(v, t, subst)
    if t.type == "var" then
        if t.name == v then return true end
        local b = subst[t.name]
        return b ~= nil and occurs(v, b, subst)
    elseif t.type == "func" then
        for _, a in ipairs(t.args) do
            if occurs(v, a, subst) then return true end
        end
    end
    return false
end

unify.occurs = occurs

local function is_var(t) return t.type == "var" end

local function deref(t, subst)
    while t.type == "var" and subst[t.name] do
        t = subst[t.name]
    end
    return t
end

-- Robinson unification over a list of (a,b) term pairs.
-- Returns substitution table or nil, errmsg.
local function unify_pairs(pairs, subst)
    subst = subst or {}
    while #pairs > 0 do
        local pair = table.remove(pairs)
        local a = deref(pair[1], subst)
        local b = deref(pair[2], subst)
        if is_var(a) then
            if a.name ~= b.name then
                if occurs(a.name, b, subst) then
                    return nil, "occurs check: " .. a.name
                end
                subst[a.name] = b
            end
        elseif is_var(b) then
            if occurs(b.name, a, subst) then
                return nil, "occurs check: " .. b.name
            end
            subst[b.name] = a
        elseif a.type ~= b.type or a.name ~= b.name then
            return nil, "clash: " .. (a.name or a.type) ..
                " vs " .. (b.name or b.type)
        elseif a.type == "func" then
            if #a.args ~= #b.args then
                return nil, "arity clash: " .. a.name
            end
            for i = 1, #a.args do
                pairs[#pairs + 1] = {a.args[i], b.args[i]}
            end
        end
        -- const/const equal names: nothing to do
    end
    return subst
end

unify.unify_pairs = unify_pairs

-- mgu of two terms: returns subst or nil, errmsg
local function mgu(a, b)
    return unify_pairs({{a, b}}, {})
end

-- mgu of two atoms (same predicate name required)
local function mgu_atoms(a, b)
    if a.name ~= b.name then
        return nil, "different predicates: " .. a.name ..
            " vs " .. b.name
    end
    if #a.args ~= #b.args then
        return nil, "arity clash: " .. a.name
    end
    local pairs = {}
    for i = 1, #a.args do pairs[i] = {a.args[i], b.args[i]} end
    return unify_pairs(pairs, {})
end

unify.mgu = mgu
unify.mgu_atoms = mgu_atoms

-- render a substitution {x↦a, y↦f(z)} course-style
local function render_subst(subst)
    local names = {}
    for v in pairs(subst) do names[#names + 1] = v end
    table.sort(names)
    local parts = {}
    for _, v in ipairs(names) do
        parts[#parts + 1] = v .. "↦" .. formula.render_term(subst[v])
    end
    return "{" .. table.concat(parts, ", ") .. "}"
end

unify.render_subst = render_subst

return unify
