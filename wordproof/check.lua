-- wordproof/check.lua — verification: exhaustive instance checking,
-- strict per-step rule checking, chain assembly.
--
-- Two verification layers:
--   * instance check: evaluate every line on all envs of a small finite
--     domain (words over Σ up to maxlen x number ranges; bound vars are
--     derived via section.bind).  Sound for rejection; enumerable.
--   * strict check: per adjacent pair, equality under
--     ambient | cited rules | {IH if cited}.  Verifies that an IH citation
--     is *necessary* (step must fail without it).

local T = require "wordproof.term"
local unpack = unpack or table.unpack
local M = {}

local function contains_nvar(t, v)
    if t.k=="nvar" then return t.s==v end
    for _,c in pairs(t) do
        if type(c)=="table" then
            if c.k and contains_nvar(c,v) then return true end
            if not c.k then
                for _,x in pairs(c) do
                    if type(x)=="table" and x.k and contains_nvar(x,v) then
                        return true end
                end
            end
        end
    end
    return false
end

local function vars_of(t, acc)
    acc = acc or {}
    if t.k=="var" or t.k=="nvar" or t.k=="lvar" then acc[t.s]=true end
    for _,c in pairs(t) do
        if type(c)=="table" then
            if c.k then vars_of(c, acc)
            else
                for _,x in pairs(c) do
                    if type(x)=="table" and x.k then vars_of(x, acc) end
                end
            end
        end
    end
    return acc
end

local function has_hole(t)
    if t.k=="hole" then return true end
    for _,c in pairs(t) do
        if type(c)=="table" then
            if c.k and has_hole(c) then return true end
            if not c.k then
                for _,x in pairs(c) do
                    if type(x)=="table" and x.k and has_hole(x) then
                        return true end
                end
            end
        end
    end
    return false
end

-- ============ rule library ============
M.rules = {}

M.rules.def_R = function(t)                 -- (u a)^R -> a·u^R
    if t.k=="rev" and t.t.k=="cat" then
        local p = t.t.parts
        local last = p[#p]
        if last.k~="lit" and last.k~="lvar" then return nil end
        local rest={}; for i=1,#p-1 do rest[i]=p[i] end
        return T.cat{last, T.rev(#rest==1 and rest[1] or T.cat(rest))}
    end
end

M.rules.thm216 = function(t)                -- (xy..z)^R -> z^R..x^R
    if t.k=="rev" and t.t.k=="cat" then
        local p, out = t.t.parts, {}
        for i=#p,1,-1 do out[#out+1]=T.rev(p[i]) end
        return T.cat(out)
    end
end

M.rules.aR = function(t)
    if t.k=="rev" and (t.t.k=="lit" or t.t.k=="lvar") then return t.t end
end

M.rules.lamR = function(t)
    if t.k=="rev" and t.t.k=="lam" then return T.LAM end
end

M.rules.rev_rev = function(t)               -- (x^R)^R -> x   (claim of 1.1b!)
    if t.k=="rev" and t.t.k=="rev" then return t.t.t end
end

M.rules.mul_into_sum = function(t)          -- A·Σ_i B -> Σ_i (A·B)
    if t.k~="nmul" then return nil end
    local others, sumt = {}, nil
    for _,f in ipairs(t.ts) do
        if f.k=="nsum" and not sumt then sumt=f else others[#others+1]=f end
    end
    if not sumt then return nil end
    for _,f in ipairs(others) do
        if contains_nvar(f, sumt.v) then return nil end
    end
    others[#others+1] = sumt.body
    return T.nsum(sumt.v, sumt.lo, sumt.hi, T.nmul(others))
end

M.rules.sum_shift = function(t)             -- Σ_{i=lo}^{hi} b^(i+c) -> Σ_{i=lo+c}^{hi+c} b^i
    if t.k~="nsum" then return nil end
    local b = t.body
    if b.k~="npow" then return nil end
    local e = b.e
    if e.k~="nadd" then return nil end
    local c, has_v = 0, false
    for _,x in ipairs(e.ts) do
        if x.k=="nvar" and x.s==t.v then has_v=true
        elseif x.k=="num" then c=c+x.n
        else return nil end
    end
    if not (has_v and c~=0) then return nil end
    return T.nsum(t.v, T.nadd{t.lo,T.num(c)}, T.nadd{t.hi,T.num(c)},
                  T.npow(b.b, T.nvar(t.v)))
end

M.rules.absorb_lo = function(t)             -- B(lo-1) + Σ_{i=lo}^{hi} B -> Σ_{i=lo-1}^{hi} B
    if t.k~="nadd" then return nil end
    for si,s in ipairs(t.ts) do
        if s.k=="nsum" then
            local lo1 = T.nadd{s.lo, T.num(-1)}
            local target = T.nf(T.subst(s.body, s.v, lo1), {})
            for ai,a in ipairs(t.ts) do
                if ai~=si and T.t_eq(T.nf(a,{}), target) then
                    local ts={}
                    for j,x in ipairs(t.ts) do
                        if j~=si and j~=ai then ts[#ts+1]=x end end
                    ts[#ts+1] = T.nsum(s.v, lo1, s.hi, s.body)
                    return T.nadd(ts)
                end
            end
        end
    end
end

M.rule_bundles = {
    arith = {M.rules.mul_into_sum, M.rules.sum_shift, M.rules.absorb_lo},
}

-- ============ domains / environments ============

local function gen_words(sigma, maxlen)
    local w = {""}
    for len=1,maxlen do
        local base = #w
        for idx=1,#w do
            local x=w[idx]
            if #x==len-1 then
                for _,a in ipairs(sigma) do w[#w+1]=x..a end
            end
        end
    end
    return w
end

-- section.bind_parsed = {varname -> term} : derived instead of ranged.
-- section == nil or opts.all_nvars → ALL declared number vars range
-- (used for validating a student-entered IH as a universal identity,
-- and for free-mode rows).  opts.extra lists additional (fresh)
-- variable names to range.
function M.envs(task, section, opts)
    opts = opts or {}
    local bind = (section and section.bind_parsed) or {}
    local words = gen_words(task.sigma or {"a","b"},
                            (task.dom and task.dom.maxlen) or 3)
    local used = opts.used          -- nil = range everything declared
    local wvars, lvars = {}, {}
    for _,s in ipairs(task.spec.wvar_list or {}) do
        if not bind[s] and (not used or used[s]) then
            wvars[#wvars+1]=s end end
    for _,s in ipairs(task.spec.lvar_list or {}) do
        if not bind[s] and (not used or used[s]) then
            lvars[#lvars+1]=s end end
    local names = (section==nil or opts.all_nvars)
        and (task.spec.nvar_list or {})
        or  ((task.dom and task.dom.num_order) or {})
    local order = {}
    for _,nm in ipairs(names) do
        if not bind[nm] and (not used or used[nm]) then
            order[#order+1]=nm end end
    for _,nm in ipairs(opts.extra or {}) do
        if not bind[nm] and (not used or used[nm]) then
            order[#order+1]=nm end end
    local envs = {}
    local function rec(idx, env)
        if idx<=#wvars then
            for _,w in ipairs(words) do
                env.words[wvars[idx]]=w; rec(idx+1,env)
            end; return
        end
        local li = idx-#wvars
        if li<=#lvars then
            for _,a in ipairs(task.sigma or {"a","b"}) do
                env.letters[lvars[li]]=a; rec(idx+1,env)
            end; return
        end
        local ni = idx-#wvars-#lvars
        if ni<=#order then
            local nm = order[ni]
            local lo,hi = unpack((task.dom and task.dom.nums
                                  and task.dom.nums[nm]) or {0,4})
            for v=lo,hi do env.nums[nm]=v; rec(idx+1,env) end
            return
        end
        -- all free vars assigned: derive bound vars, then SNAPSHOT
        for name,bt in pairs(bind) do
            local v = T.eval(bt, env)
            if T.domain(bt)=="num" then env.nums[name]=v
            else env.words[name]=v end
        end
        local w2,l2,n2 = {},{},{}
        for k,v in pairs(env.words)   do w2[k]=v end
        for k,v in pairs(env.letters) do l2[k]=v end
        for k,v in pairs(env.nums)    do n2[k]=v end
        envs[#envs+1]={words=w2, letters=l2, nums=n2, f=env.f}
    end
    rec(1, {words={}, letters={}, nums={}, f=task.f_eval})
    return envs
end

local function show_env(env)
    local p={}
    for k,v in pairs(env.words) do p[#p+1]=k.."="..(v=="" and "λ" or v) end
    for k,v in pairs(env.letters) do p[#p+1]=k.."="..v end
    for k,v in pairs(env.nums) do p[#p+1]=k.."="..v end
    table.sort(p)
    return table.concat(p,", ")
end
M.show_env = show_env

-- ============ instance check ============
local function instance_ok(t1, t2, envs)
    for _,e in ipairs(envs) do
        local ok1,v1 = pcall(T.eval, t1, e)
        local ok2,v2 = pcall(T.eval, t2, e)
        if not ok1 then return false, {err=tostring(v1), env=show_env(e)} end
        if not ok2 then return false, {err=tostring(v2), env=show_env(e)} end
        if v1~=v2 then
            return false, {env=show_env(e), lv=tostring(v1), rv=tostring(v2)}
        end
    end
    return true
end
M.instance_ok = instance_ok

-- ============ strict step check ============
-- step_ok(E1, E2, fns, expand, ih): are E1,E2 equal under
--   ambient ∪ fns (fixpoint) ∪ optional bounded search:
--     expand → one definition expansion per pow position,
--     ih     → ≤2 applications of the IH rules (either direction).
-- IH stays OUT of the fixpoint set: its two directions would oscillate.
local function cand_normal_forms(t0, fns, expand, ih)
    local seen, cands, frontier = {}, {}, {}
    local function push(v, is_frontier)
        local k = T.show(v)
        if seen[k] then return false end
        seen[k] = true
        cands[#cands+1] = v
        if is_frontier then frontier[#frontier+1] = v end
        return true
    end
    push(T.nf(t0, fns), true)
    if expand then
        local prev = frontier; frontier = {}
        for _,x in ipairs(prev) do
            for _,v in ipairs(T.expansions(x)) do
                push(T.nf(v, fns), true)
            end
        end
    end
    if ih then
        for _=1,2 do
            if #frontier==0 then break end
            local prev = frontier; frontier = {}
            for _,x in ipairs(prev) do
                for _,r in ipairs(ih) do
                    for _,v in ipairs(T.applications(r, x)) do
                        local nv = T.nf(v, fns)
                        if push(nv) then frontier[#frontier+1] = nv end
                    end
                end
            end
        end
    end
    local nfs = {}
    for _,v in ipairs(cands) do nfs[#nfs+1] = v end
    return nfs
end

local function step_ok(E1, E2, fns, expand, ih)
    local c1 = cand_normal_forms(E1, fns, expand, ih)
    local c2 = cand_normal_forms(E2, fns, expand, ih)
    for _,a in ipairs(c1) do
        for _,b in ipairs(c2) do
            if T.t_eq(a, b) then return true end
        end
    end
    return false
end
M.step_ok = step_ok

-- ============ IH machinery ============
local function build_ih(task, ih_lhs, ih_rhs)
    local names = {}
    local function scan(t)
        if t.k=="var" or t.k=="nvar" or t.k=="lvar" then names[t.s]=t.k end
        for _,c in pairs(t) do
            if type(c)=="table" then
                if c.k then scan(c)
                else for _,x in pairs(c) do
                    if type(x)=="table" and x.k then scan(x) end end
                end
            end
        end
    end
    scan(ih_lhs); scan(ih_rhs)
    local restrict = {}
    for name,kd in pairs(names) do
        if kd=="nvar" then
            restrict[name] = function(t)
                return t.k=="nvar" and t.s==name end
        elseif kd=="var" and task.small_vars and task.small_vars[name] then
            restrict[name] = function(t)
                return t.k=="var" and t.s==name end
        elseif kd=="var" then
            restrict[name] = function(t) return T.domain(t)=="word" end
        elseif kd=="lvar" then
            restrict[name] = function(t)
                return t.k=="lvar" and t.s==name end
        end
    end
    return { T.rule_from_pattern(ih_lhs, ih_rhs, restrict),
             T.rule_from_pattern(ih_rhs, ih_lhs, restrict) }
end
M.build_ih = build_ih

local function fires_on(rules, t)
    for _,r in ipairs(rules) do
        if #T.applications(r, t) > 0 then return true end
    end
    return false
end

-- ============ resolve citations ============
local function resolve_cites(task, cite_label, ih_fns)
    -- returns fns(without IH), ih_cited, expand
    local fns, ih, expand = {}, false, false
    for cname in tostring(cite_label or ""):gmatch("[^;]+") do
        local cn = cname:match("^%s*(.-)%s*$")
        local mapped = task.cite_map and task.cite_map[cn]
        if mapped then
            for _,r in ipairs(mapped) do
                if r=="IH" then ih=true
                elseif r=="EXPAND" then expand=true
                elseif type(r)=="table" then
                    for _,rr in ipairs(r) do fns[#fns+1]=rr end
                else fns[#fns+1]=r end
            end
        end
    end
    return fns, ih, expand
end

-- ============ top-level check ============
-- input = { ih = "l = r" (free mode, overrides task.ih_str),
--           sections = { [si] = {bind_str="u a" (free), rows={ {expr,cite} }} } }
-- For skeleton mode rows may carry expr_parsed (templates filled by caller).
-- Sections may be sparse: only keys present in input.sections are checked.

-- identify the induction's step variable: match the goal's lhs (with the
-- induction variable as metavariable) against the IH's lhs; whatever sits
-- at that position is the step variable.  Returns nil when the IH does not
-- have the goal's shape.
local function detect_step_var(task, ih_lhs)
    if not (task.goal_lhs and task.indvar) then return nil end
    local env = T.match(task.goal_lhs, ih_lhs,
                        {[task.indvar] = function() return true end})
    local b = env and env[task.indvar]
    if b and b.k=="nvar" then return b.s end
end

function M.check(task, input)
    local res = {ok=true, sections={}, msg=nil}

    -- fresh (undeclared) number vars the student may introduce as their
    -- step variable; parsed lazily into the spec on demand.
    local fresh = {}
    local function eff_spec()
        if not next(fresh) then return task.spec end
        local s = {}
        for k,v in pairs(task.spec) do
            if type(v)=="table" then
                local t={}; for a,b in pairs(v) do t[a]=b end; s[k]=t
            else s[k]=v end
        end
        s.nvar = s.nvar or {}
        s.nvar_list = {}
        for v in pairs(fresh) do s.nvar[v]=true end
        for v in pairs(s.nvar) do s.nvar_list[#s.nvar_list+1]=v end
        table.sort(s.nvar_list)
        return s
    end
    local function fresh_list()
        local t={}; for v in pairs(fresh) do t[#t+1]=v end
        table.sort(t); return t
    end
    -- parse an equation, allowing unknown single-letter number vars to be
    -- introduced (the student's free choice of step variable)
    local function parse_eq_relaxed(src)
        local l, r
        for _=1,6 do
            l, r = T.parse_eq(src, eff_spec())
            if l then return l, r end
            local c = tostring(r):match("'(%a)' is not a number symbol")
            if not c or fresh[c] then return nil, r end
            fresh[c] = true
        end
        return nil, r
    end

    -- IH: task-provided (skeleton) or student equation (free)
    local ih_fns = task.ih_fns
    local step_var = task.step_var
    if input.ih and input.ih ~= "" then
        local l,r = parse_eq_relaxed(input.ih)
        if not l then
            res.ok=false; res.ih={kind="parse", msg=tostring(r)}
        else
            -- must be a valid identity on the unconstrained domain
            local ihused = vars_of(l, vars_of(r))
            local envs0 = M.envs(task, nil,
                {extra=fresh_list(), used=ihused})
            local ok,cex = instance_ok(l, r, envs0)
            if not ok then
                res.ok=false
                res.ih={kind="instance_fail",
                        msg="the IH is not a valid identity", cex=cex}
            else
                ih_fns = build_ih(task, l, r)
                res.ih={kind="ok"}
                local sv = detect_step_var(task, l)
                if sv then step_var = sv; res.ih.step_var = sv end
                if task.goal_lhs and task.goal_rhs
                   and (fires_on(ih_fns, task.goal_lhs)
                        or fires_on(ih_fns, task.goal_rhs)) then
                    res.ok=false
                    res.ih={kind="circular",
                            msg="the IH rewrites the claim itself — circular"}
                end
            end
        end
    end
    res.ih_fns_count = ih_fns and #ih_fns or 0
    res.step_var = step_var

    local any_ih_step = false

    local sis = {}
    for si in pairs(input.sections or {}) do sis[#sis+1]=si end
    table.sort(sis)

    for _,si in ipairs(sis) do
        local sec = input.sections[si]
        local task_sec = task.sections and task.sections[si]
        local sres = {links={}, rows={}}
        res.sections[si] = sres

        -- premises: in free mode the student must state them (bind_str);
        -- in skeleton mode the section's declared bind applies.
        local sec_bind = nil
        if sec.bind_str and sec.bind_str ~= "" then
            local bp = {}
            for eq in sec.bind_str:gmatch("[^,]+") do
                local v,e = T.parse_eq(eq, eff_spec())
                if v and (v.k=="var" or v.k=="nvar") then bp[v.s]=e
                else
                    sres.msg="cannot parse premise: "..eq
                    res.ok=false
                end
            end
            sec_bind = bp
        elseif not task.free and task_sec then
            sec_bind = task_sec.bind_parsed
        end
        local bindmap = sec_bind

        local terms, raw_terms = {}, {}
        local n = #(sec.rows or {})
        for i=1,n do
            local row = sec.rows[i]
            local t = row.expr_parsed
            if not t and (row.expr or ""):match("^%s*$") then
                sres.rows[i]={kind="empty", msg="(empty)"}
            elseif not t then
                local ok,pt = pcall(T.parse, row.expr or "", eff_spec())
                if ok then t=pt
                else
                    sres.rows[i]={kind="parse",
                        msg=(type(pt)=="table" and pt.__perr) or tostring(pt)}
                end
            end
            if t and has_hole(t) then
                sres.rows[i]={kind="empty", msg="(fill in)"}
                t=nil
            end
            raw_terms[i]=t
            -- apply the section's bind premises symbolically, so the strict
            -- checker sees ((u·a)^R)^R where the student wrote (w^R)^R
            if t and bindmap then
                for v,bt in pairs(bindmap) do t=T.subst(t,v,bt) end
            end
            terms[i]=t
            sres.rows[i] = sres.rows[i] or {kind="ok"}
        end

        -- domain: only range variables the section actually uses
        -- (rows + premise right-hand sides)
        local used = {}
        for i=1,n do
            if raw_terms[i] then vars_of(raw_terms[i], used) end
        end
        for _,bt in pairs(bindmap or {}) do vars_of(bt, used) end
        local envs = M.envs(task, {bind_parsed=sec_bind},
            {extra=fresh_list(), all_nvars = task.free or nil, used=used})

        -- free mode: the chain must begin/end at the section's endpoints
        -- (e.g. start at (w^R)^(k+1), end at (w^(k+1))^R).  Optional
        -- sections only check when they contain rows.
        if task.free and task_sec and task_sec.expect_first then
            local fi, li
            for i=1,n do
                if terms[i] then fi = fi or i; li = i end
            end
            if fi then
                local function expected(t0)
                    local e = t0
                    if task.step_var and step_var ~= task.step_var then
                        e = T.subst(e, task.step_var, T.nvar(step_var))
                    end
                    if bindmap then
                        for v,bt in pairs(bindmap) do e=T.subst(e,v,bt) end
                    end
                    return e
                end
                local ef = expected(task_sec.expect_first)
                local el = expected(task_sec.expect_last
                                    or task_sec.expect_first)
                if not T.t_eq(terms[fi], ef) then
                    sres.rows[fi] = {kind="endpoint",
                        msg="start the chain at "..T.show(ef)}
                    res.ok = false
                end
                if not T.t_eq(terms[li], el) then
                    sres.rows[li] = {kind="endpoint",
                        msg="end the chain at "..T.show(el)}
                    res.ok = false
                end
            end
        end

        for j=1,n-1 do
            local a,b = terms[j], terms[j+1]
            local row = sec.rows[j+1] or {}
            local link = {idx=j, cite=row.cite}
            sres.links[j]=link
            if not (a and b) then
                link.kind="pending"
                res.ok=false          -- an open link is not a proof
            elseif T.t_eq(raw_terms[j], raw_terms[j+1]) then
                -- noop on the *unsubstituted* terms: the bind line
                -- "(w^R)^R = ((ua)^R)^R" differs pre-substitution and is
                -- a legitimate instantiation step, not a no-op.
                link.kind="noop"
                link.msg="no progress: the two lines are identical"
                res.ok=false
            else
                local fns, ih_cited, expand = resolve_cites(task, row.cite, ih_fns)
                local ih_for_step = nil
                if ih_cited then
                    if ih_fns then
                        ih_for_step = ih_fns
                        any_ih_step = true
                    else
                        link.kind="missing_ih"
                        link.msg="IH cited, but no induction hypothesis was given"
                        res.ok=false
                    end
                end
                if not link.kind then
                    local ok,cex = instance_ok(a,b,envs)
                    if not ok then
                        link.kind="instance_fail"; link.cex=cex; res.ok=false
                    else
                        link.kind="ok"
                        if (#fns>0 or ih_cited or expand)
                           and not step_ok(a,b,fns,expand,ih_for_step) then
                            link.kind="mismatch"
                            link.msg="numerically true, but does not follow "
                                   .."from the cited rules"
                            res.ok=false
                        elseif ih_cited then
                            local noih = resolve_cites(task, row.cite, nil)
                            if step_ok(a,b,noih,expand) then
                                link.kind="ih_unnecessary"
                                link.msg="also holds without the IH"
                            end
                        end
                    end
                end
            end
        end
    end

    if task.require_ih and (input.ih or task.ih_str) and not any_ih_step then
        res.ok=false
        res.msg = res.msg or "the induction hypothesis is never used — "
                          .."cite 'IH' in the induction step"
    end
    return res
end

return M
