-- Semantics: evaluate formulas.
-- eval_prop(ast, valuation)         -- valuation: {atomname -> bool}
-- eval(ast, interp, assignment)     -- predicate logic
--
-- interp = {
--   domain = {elem, ...}            -- non-empty list of domain elems
--   constants = {name -> elem}      -- constants (default: name itself
--                                   -- if in domain)
--   functions = {name -> fn|table}  -- arity-consistent; table keyed
--                                   -- by tuple "e1,e2,.."
--   predicates = {name -> pred}     -- pred = function(...) -> bool,
--                                   -- or set of tuples {["a,b"]=true},
--                                   -- or for arity 1 set {a=true}
-- }
-- assignment = {varname -> elem}    -- for free variables

local eval = {}
local unpack = unpack or table.unpack

local function eval_term(t, interp, asg)
    if t.type == "var" then
        local v = asg and asg[t.name]
        if v == nil then
            error("unassigned variable " .. t.name)
        end
        return v
    elseif t.type == "const" then
        local c = interp.constants and interp.constants[t.name]
        if c == nil then
            -- convention: uninterpreted constant denotes itself
            return t.name
        end
        return c
    else -- func
        local args = {}
        for i, a in ipairs(t.args) do
            args[i] = eval_term(a, interp, asg)
        end
        local f = interp.functions and interp.functions[t.name]
        if f == nil then
            error("no interpretation for function " .. t.name)
        end
        if type(f) == "function" then
            return f(unpack(args))
        end
        return f[table.concat(args, ",")]
    end
end

local function pred_holds(name, args, interp)
    local p = interp.predicates and interp.predicates[name]
    if p == nil then
        error("no interpretation for predicate " .. name)
    end
    if type(p) == "function" then
        return not not p(unpack(args))
    end
    if #args == 1 then
        return p[args[1]] == true or p[args[1]] ~= nil
            and p[args[1]] ~= false
    end
    return p[table.concat(args, ",")] == true
end

local OPS = {
    ["not"]= function(a) return not a end,
    ["and"]= function(a, b) return a and b end,
    ["or"] = function(a, b) return a or b end,
    nand   = function(a, b) return not (a and b) end,
    nor    = function(a, b) return not (a or b) end,
    imp    = function(a, b) return (not a) or b end,
    revimp = function(a, b) return a or (not b) end,
    iff    = function(a, b) return a == b end,
    xor    = function(a, b) return a ~= b end,
}

-- map ast op keys to truth functions
local BIN = {
    ["and"]  = OPS["and"],
    ["or"]   = OPS["or"],
    nand     = OPS.nand,
    nor      = OPS.nor,
    imp      = OPS.imp,
    revimp   = OPS.revimp,
    iff      = OPS.iff,
    xor      = OPS.xor,
}

local function eval_formula(f, interp, asg)
    if f.type == "true" then return true end
    if f.type == "false" then return false end
    if f.type == "atom" then
        local args = {}
        for i, a in ipairs(f.args) do
            args[i] = eval_term(a, interp, asg)
        end
        return pred_holds(f.name, args, interp)
    elseif f.type == "op" then
        if f.op == "not" then
            return not eval_formula(f.args[1], interp, asg)
        end
        local l = eval_formula(f.args[1], interp, asg)
        if f.op == "and" and not l then return false end
        if f.op == "or" and l then return true end
        local r = eval_formula(f.args[2], interp, asg)
        return BIN[f.op](l, r)
    elseif f.type == "quant" then
        local dom = interp.domain
        local function try(i)
            if i > #f.vars then
                return eval_formula(f.body, interp, asg)
            end
            local v = f.vars[i].name
            if f.quant == "forall" then
                for _, e in ipairs(dom) do
                    asg[v] = e
                    if not try(i + 1) then
                        asg[v] = nil
                        return false
                    end
                end
                asg[v] = nil
                return true
            else
                for _, e in ipairs(dom) do
                    asg[v] = e
                    if try(i + 1) then
                        asg[v] = nil
                        return true
                    end
                end
                asg[v] = nil
                return false
            end
        end
        return try(1)
    end
end

eval.eval_term = eval_term

function eval.eval(f, interp, asg)
    return eval_formula(f, interp, asg or {})
end

-- propositional: valuation maps atom name -> bool
function eval.eval_prop(f, valuation)
    local interp = {
        domain = {},
        predicates = setmetatable({}, {__index = function(_, name)
            return function() return valuation[name] == true end
        end}),
        constants = {},
        functions = {},
    }
    local function w(n)
        if n.type == "atom" and #n.args > 0 then
            error("eval_prop: non-propositional atom " .. n.name)
        elseif n.type == "op" then
            for _, a in ipairs(n.args) do w(a) end
        elseif n.type == "quant" then
            error("eval_prop: quantifier in propositional formula")
        end
    end
    w(f)
    return eval_formula(f, interp, {})
end

return eval
