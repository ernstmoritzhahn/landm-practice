-- wordproof/term.lua — Term algebra for induction proofs over words & numbers.
--
-- Word terms : lam lit lvar var cat rev pow(b, numexpr)
-- Num  terms : num nvar nadd{} nmul{} npow nsum{v,lo,hi,body} fapp{fn,arg}
-- Hole      : {k="hole"} — placeholder in skeleton templates (student input).
--
-- Pure Lua 5.1+: runs on luajit(52compat) in the container and in the
-- lua-5.4 wasm runtime used by html/*.html workbenches.

local M = {}
local unpack = table.unpack or unpack

-- ============ constructors ============
M.LAM = {k="lam"}
function M.lit(s)  return {k="lit",s=s} end       -- concrete letter
function M.lvar(s) return {k="lvar",s=s} end      -- meta-letter (ranges over Σ)
function M.var(s)  return {k="var",s=s} end       -- word variable
function M.cat(p)  return {k="cat",parts=p} end
function M.rev(t)  return {k="rev",t=t} end
function M.pow(b,e) return {k="pow",b=b,e=e} end  -- word^numexpr
function M.hole()  return {k="hole"} end
function M.num(n)  return {k="num",n=n} end
function M.nvar(s) return {k="nvar",s=s} end
function M.nadd(ts) return {k="nadd",ts=ts} end
function M.nmul(ts) return {k="nmul",ts=ts} end
function M.npow(b,e) return {k="npow",b=b,e=e} end
function M.nsum(v,lo,hi,body) return {k="nsum",v=v,lo=lo,hi=hi,body=body} end
function M.fapp(fn,arg) return {k="fapp",fn=fn,arg=arg} end

local WORDK = {lam=1,lit=1,lvar=1,var=1,cat=1,rev=1,pow=1}
local NUMK  = {num=1,nvar=1,nadd=1,nmul=1,npow=1,nsum=1,fapp=1}
function M.domain(t)
    if WORDK[t.k] then return "word" end
    if NUMK[t.k] then return "num" end
    return "hole"
end

-- ============ pretty printing ============
local function prec(t)            -- for parenthesizing
    if t.k=="cat" or t.k=="nadd" then return 2 end
    if t.k=="nmul" then return 4 end
    if t.k=="rev" or t.k=="pow" or t.k=="npow" then return 7 end
    return 9
end

local show
local function shownum(e, parent_prec)
    local s
    if e.k=="num" then s=tostring(e.n)
    elseif e.k=="nvar" then s=e.s
    elseif e.k=="nadd" then
        local p={}; for _,x in ipairs(e.ts) do p[#p+1]=shownum(x,2) end
        s=table.concat(p,"+")
        if parent_prec and parent_prec>2 then s="("..s..")" end
        return s
    elseif e.k=="nmul" then
        local p={}; for _,x in ipairs(e.ts) do p[#p+1]=shownum(x,4) end
        s=table.concat(p,"·")
        if parent_prec and parent_prec>4 then s="("..s..")" end
        return s
    elseif e.k=="npow" then
        s=shownum(e.b,8).."^"..shownum(e.e,5)
    elseif e.k=="nsum" then
        s="Σ_{"..e.v.."="..shownum(e.lo).."}^{"..shownum(e.hi).."} "..shownum(e.body,3)
        if parent_prec and parent_prec>3 then s="("..s..")" end
        return s
    elseif e.k=="fapp" then s=e.fn.."("..shownum(e.arg)..")"
    elseif e.k=="hole" then s="□"
    else s="?" end
    if parent_prec and parent_prec>8 then s="("..s..")" end
    return s
end
M.shownum = shownum

show = function(t)
    if t.k=="lam" then return "λ"
    elseif t.k=="lit" or t.k=="lvar" then return t.s
    elseif t.k=="var" then return t.s
    elseif t.k=="hole" then return "□"
    elseif t.k=="rev" then
        local inner = show(t.t)
        return (prec(t.t)<9 and "("..inner..")" or inner).."^R"
    elseif t.k=="pow" then
        local inner = show(t.b)
        return (prec(t.b)<9 and "("..inner..")" or inner).."^"..shownum(t.e,5)
    elseif t.k=="cat" then
        local p={}; for _,x in ipairs(t.parts) do
            local s=show(x); p[#p+1]=(prec(x)<2 and "("..s..")" or s)
        end
        return table.concat(p,"·")
    elseif NUMK[t.k] then return shownum(t)
    end
    return "?"
end
M.show = show

local function show_html(t)
    if t.k=="lam" then return "λ"
    elseif t.k=="lit" or t.k=="lvar" or t.k=="var" then return t.s
    elseif t.k=="hole" then return "□"
    elseif t.k=="rev" then
        local inner=show_html(t.t)
        return (prec(t.t)<9 and "("..inner..")" or inner).."<sup>R</sup>"
    elseif t.k=="pow" then
        local inner=show_html(t.b)
        return (prec(t.b)<9 and "("..inner..")" or inner)
               .."<sup>"..shownum(t.e,5).."</sup>"
    elseif t.k=="cat" then
        local p={}; for _,x in ipairs(t.parts) do
            local s=show_html(x); p[#p+1]=(prec(x)<2 and "("..s..")" or s)
        end
        return table.concat(p,"·")
    elseif NUMK[t.k] then
        local e=t
        if e.k=="npow" then return show_html(e.b).."<sup>"..shownum(e.e,5).."</sup>"
        elseif e.k=="nsum" then
            return "Σ<sub>"..e.v.."="..shownum(e.lo).."</sub><sup>"..shownum(e.hi).."</sup> "..show_html(e.body)
        end
    end
    return show(t)
end
M.show_html = show_html

-- ============ equality ============
local function t_eq(a,b)
    if a.k~=b.k then return false end
    if a.k=="lit" or a.k=="lvar" or a.k=="var" or a.k=="nvar" then return a.s==b.s end
    if a.k=="num" then return a.n==b.n end
    if a.k=="lam" or a.k=="hole" then return true end
    if a.k=="rev" then return t_eq(a.t,b.t) end
    if a.k=="pow" or a.k=="npow" then return t_eq(a.b,b.b) and t_eq(a.e,b.e) end
    if a.k=="cat" then
        if #a.parts~=#b.parts then return false end
        for i=1,#a.parts do if not t_eq(a.parts[i],b.parts[i]) then return false end end
        return true
    end
    if a.k=="nadd" or a.k=="nmul" then
        if #a.ts~=#b.ts then return false end
        for i=1,#a.ts do if not t_eq(a.ts[i],b.ts[i]) then return false end end
        return true
    end
    if a.k=="nsum" then return a.v==b.v and t_eq(a.lo,b.lo) and t_eq(a.hi,b.hi) and t_eq(a.body,b.body) end
    if a.k=="fapp" then return a.fn==b.fn and t_eq(a.arg,b.arg) end
    return false
end
M.t_eq = t_eq

-- ============ substitution ============
-- subst(t, name, repl): replace var/nvar/lvar named `name` by `repl`.
local function subst(t, name, repl)
    if (t.k=="var" or t.k=="nvar" or t.k=="lvar") and t.s==name then return repl end
    if t.k=="rev" then return M.rev(subst(t.t,name,repl)) end
    if t.k=="pow" then return M.pow(subst(t.b,name,repl), subst(t.e,name,repl)) end
    if t.k=="cat" then
        local p={}; for _,x in ipairs(t.parts) do p[#p+1]=subst(x,name,repl) end
        return M.cat(p)
    end
    if t.k=="nadd" or t.k=="nmul" then
        local p={}; for _,x in ipairs(t.ts) do p[#p+1]=subst(x,name,repl) end
        return {k=t.k,ts=p}
    end
    if t.k=="npow" then return M.npow(subst(t.b,name,repl), subst(t.e,name,repl)) end
    if t.k=="nsum" then
        if t.v==name then return t end   -- bound variable shadows
        return M.nsum(t.v, subst(t.lo,name,repl), subst(t.hi,name,repl), subst(t.body,name,repl))
    end
    if t.k=="fapp" then return M.fapp(t.fn, subst(t.arg,name,repl)) end
    return t
end
M.subst = subst

-- fill the (single) hole marker in a template term
function M.fill_hole(t, hole)
    if t.k=="hole" then return hole end
    if t.k=="rev" then return M.rev(M.fill_hole(t.t,hole)) end
    if t.k=="pow" then return M.pow(M.fill_hole(t.b,hole), M.fill_hole(t.e,hole)) end
    if t.k=="cat" then
        local p={}; for _,x in ipairs(t.parts) do p[#p+1]=M.fill_hole(x,hole) end
        return M.cat(p)
    end
    if t.k=="nadd" or t.k=="nmul" then
        local p={}; for _,x in ipairs(t.ts) do p[#p+1]=M.fill_hole(x,hole) end
        return {k=t.k,ts=p}
    end
    if t.k=="npow" then return M.npow(M.fill_hole(t.b,hole), M.fill_hole(t.e,hole)) end
    if t.k=="nsum" then
        return M.nsum(t.v, M.fill_hole(t.lo,hole), M.fill_hole(t.hi,hole), M.fill_hole(t.body,hole))
    end
    if t.k=="fapp" then return M.fapp(t.fn, M.fill_hole(t.arg,hole)) end
    return t
end

-- ============ parser ============
-- spec = { lit={a=1}, lvar={a=1}, wvar={w=1,u=1,v=1}, nvar={i=1,k=1,n=1},
--          fns={f=1} }
-- Syntax:  word := juxtaposed atoms;  x^R  x^{k+1}  ( ... )  λ ε ∅  ?
--          num  := n+m | n·m | n m | n^m | f(n) | sum(i,lo,hi;body) | Σ(i,...)
local function normalize_input(s)
    s = s:gsub("λ","\1"):gsub("ε","\1"):gsub("∅","\1")
         :gsub("Σ","\2"):gsub("·","*"):gsub("λ","\1")
    return s
end

function M.parse(src, spec)
    src = normalize_input(src)
    local i, n = 1, #src
    local function skipws() while src:sub(i,i)==" " do i=i+1 end end
    local function peek()
        skipws()
        return src:sub(i,i)
    end
    local function fail(msg) error({__perr=msg, pos=i}, 0) end

    local function declared_desc()
        local function keys(m)
            local t={}; for s in pairs(m or {}) do t[#t+1]=s end
            table.sort(t); return table.concat(t,", ")
        end
        local p={}
        if spec.wvar and next(spec.wvar) then p[#p+1]="word vars: "..keys(spec.wvar) end
        if spec.lvar and next(spec.lvar) then p[#p+1]="letter vars: "..keys(spec.lvar) end
        if spec.lit and next(spec.lit) then p[#p+1]="letters: "..keys(spec.lit) end
        if spec.nvar and next(spec.nvar) then p[#p+1]="number vars: "..keys(spec.nvar) end
        if spec.fns and next(spec.fns) then p[#p+1]="functions: "..keys(spec.fns) end
        return #p>0 and ("declared: "..table.concat(p,"; "))
                    or "no symbols declared"
    end

    local parse_word, parse_num, parse_nexpr, parse_nfact, parse_nbase  -- fwd decls

    local function ident_kind(ch)
        -- single-char identifier classification
        if ch=="R" then return nil end                 -- postfix modifier
        if spec.lit and spec.lit[ch] then return "lit" end
        if spec.lvar and spec.lvar[ch] then return "lvar" end
        if spec.wvar and spec.wvar[ch] then return "var" end
        if spec.nvar and spec.nvar[ch] then return "nvar" end
        return nil
    end

    local function parse_watom()
        local c = peek()
        if c=="?" then i=i+1; return {k="hole"} end
        if c=="\1" then i=i+1; return M.LAM end
        if c=="(" then
            i=i+1
            local t = parse_word()
            if peek() ~= ")" then fail("expected )") end
            i=i+1
            return t
        end
        if c:match("%a") then
            -- keyword lambda / sum handled by caller before atoms
            local kind = ident_kind(c)
            if not kind or kind=="nvar" then
                fail("'"..c.."' is not a word symbol ("..declared_desc()..")")
            end
            i=i+1
            if kind=="lit" then return M.lit(c) end
            if kind=="lvar" then return M.lvar(c) end
            return M.var(c)
        end
        fail("expected a word symbol at "..i)
    end

    local function parse_wpost()
        local t = parse_watom()
        while true do
            local c = peek()
            if c=="^" then
                i=i+1
                if src:sub(i,i)=="R" then
                    i=i+1; t = M.rev(t)
                else
                    -- bare exponent binds tightly: only a primary (w^k, w^2,
                    -- w^f(n)); compound exponents come parenthesized (w^(k+1)).
                    t = M.pow(t, parse_nbase())
                end
            else break end
        end
        return t
    end

    parse_word = function()
        local parts = {}
        while true do
            local c = peek()
            if c=="" or c==")" or c=="=" or c=="," or c==";" then break end
            if c=="+" then break end
            if c=="*" then i=i+1  -- · as explicit concat operator
            else parts[#parts+1] = parse_wpost() end
        end
        if #parts==0 then fail("empty expression") end
        if #parts==1 then return parts[1] end
        return M.cat(parts)
    end

    parse_nbase = function()
        local c = peek()
        if c=="?" then i=i+1; return {k="hole"} end
        if c=="(" then
            i=i+1
            local t=parse_nexpr()
            if peek()~=")" then fail("expected )") end
            i=i+1; return t
        end
        if c:match("%d") then
            local j=i; while src:sub(i,i):match("%d") do i=i+1 end
            return M.num(tonumber(src:sub(j,i-1)))
        end
        if c=="\2" then i=i+1; goto do_sum end
        if c:match("%a") then
            -- keywords first
            if src:sub(i,i+3)=="sum(" or src:sub(i,i+3)=="sum " then
                i=i+3; goto do_sum
            end
            if spec.fns and spec.fns[c] and src:sub(i+1,i+1)=="(" then
                local fname=c; i=i+2
                local arg=parse_nexpr()
                if peek()~=")" then fail("expected ) after "..fname.."(") end
                i=i+1
                return M.fapp(fname,arg)
            end
            if spec.nvar and spec.nvar[c] then i=i+1; return M.nvar(c) end
            fail("'"..c.."' is not a number symbol ("..declared_desc()..")")
        end
        fail("expected a number at "..i)
        ::do_sum::
        -- already consumed "sum"/"Σ"; expect ( var , nexpr , nexpr ; nexpr )
        if peek()~="(" then fail("expected ( after sum") end
        i=i+1
        local v=peek()
        if not (spec.nvar and spec.nvar[v]) then fail("sum index must be a declared number variable") end
        i=i+1
        if peek()~="," then fail("expected , in sum") end i=i+1
        local lo=parse_nexpr()
        if peek()~="," then fail("expected , in sum") end i=i+1
        local hi=parse_nexpr()
        local sep=peek()
        if sep~=";" and sep~="," then fail("expected ; before sum body") end i=i+1
        local body=parse_nexpr()
        if peek()~=")" then fail("expected ) to close sum") end i=i+1
        return M.nsum(v,lo,hi,body)
    end

    parse_nfact = function()
        local b = parse_nbase()
        if peek()=="^" then
            i=i+1
            if src:sub(i,i)=="R" then fail("^R applies to words only") end
            local e = parse_nfact()
            return M.npow(b,e)
        end
        return b
    end

    local function parse_nmul()
        local ts = {parse_nfact()}
        while true do
            local c=peek()
            if c=="*" then i=i+1; ts[#ts+1]=parse_nfact()
            -- juxtaposition: next token can start a num factor
            elseif c~="" and c~=")" and c~="+" and c~="," and c~=";" and c~="="
                   and c~="?" and c~="\1" then
                local ch=src:sub(i,i)
                local starts = ch:match("%d") or ch=="(" or ch=="\2"
                    or (spec.nvar and spec.nvar[ch])
                    or (spec.fns and spec.fns[ch] and src:sub(i+1,i+1)=="(")
                if not starts then break end
                ts[#ts+1]=parse_nfact()
            else break end
        end
        if #ts==1 then return ts[1] end
        return M.nmul(ts)
    end

    parse_nexpr = function()
        local ts = {parse_nmul()}
        while peek()=="+" do i=i+1; ts[#ts+1]=parse_nmul() end
        if #ts==1 then return ts[1] end
        return M.nadd(ts)
    end

    -- entry: word parse first, num parse as fallback (for e.g. "(n+1)" or
    -- pure numeric chains).  A word parse that leaves trailing input also
    -- falls through to num.
    local okw, tw = pcall(function()
        i = 1
        local t = parse_word()
        skipws()
        if i<=n then fail("trailing input at "..i) end
        return t
    end)
    if okw then return tw end
    local werr = (type(tw)=="table" and tw.__perr) or tostring(tw)
    local okn, tn = pcall(function()
        i = 1
        local t = parse_nexpr()
        skipws()
        if i<=n then fail("trailing input at "..i) end
        return t
    end)
    if okn then return tn end
    fail(werr)
end

function M.parse_eq(src, spec)
    local p = src:find("=")
    if not p then return nil,"no '=' in equation" end
    local ok1,l = pcall(M.parse, src:sub(1,p-1), spec)
    if not ok1 then return nil, (type(l)=="table" and l.__perr or tostring(l)) end
    local ok2,r = pcall(M.parse, src:sub(p+1), spec)
    if not ok2 then return nil, (type(r)=="table" and r.__perr or tostring(r)) end
    return l, r
end

-- ============ evaluation ============
-- env = { words={name→str}, letters={name→str}, nums={name→int},
--         f = function(name, n, nums) -> int }
local function eval(t, env)
    if t.k=="lam" then return "" end
    if t.k=="lit" then return t.s end
    if t.k=="lvar" then
        local v = env.letters and env.letters[t.s]
        if v==nil then error("unbound letter "..t.s,0) end
        return v
    end
    if t.k=="var" then
        local v = env.words and env.words[t.s]
        if v==nil then error("unbound word variable "..t.s,0) end
        return v
    end
    if t.k=="cat" then
        local p={}; for _,x in ipairs(t.parts) do p[#p+1]=eval(x,env) end
        return table.concat(p)
    end
    if t.k=="rev" then return eval(t.t,env):reverse() end
    if t.k=="pow" then
        local e = eval(t.e,env)
        return eval(t.b,env):rep(e)
    end
    if t.k=="num" then return t.n end
    if t.k=="nvar" then
        local v = env.nums and env.nums[t.s]
        if v==nil then error("unbound number variable "..t.s,0) end
        return v
    end
    if t.k=="nadd" then
        local s=0; for _,x in ipairs(t.ts) do s=s+eval(x,env) end
        return s
    end
    if t.k=="nmul" then
        local s=1; for _,x in ipairs(t.ts) do s=s*eval(x,env) end
        return s
    end
    if t.k=="npow" then return eval(t.b,env)^eval(t.e,env) end
    if t.k=="nsum" then
        local lo,hi = eval(t.lo,env), eval(t.hi,env)
        local s=0
        for v=lo,hi do
            env.nums[t.v]=v
            s=s+eval(t.body,env)
        end
        env.nums[t.v]=nil
        return s
    end
    if t.k=="fapp" then
        if not env.f then error("function "..t.fn.." not defined",0) end
        return env.f(t.fn, eval(t.arg,env), env.nums)
    end
    if t.k=="hole" then error("unfilled hole",0) end
    error("cannot evaluate "..t.k,0)
end
M.eval = eval

-- ============ normal form ============
-- nf(t, rs): ambient normalization + rewrite rules rs (list of fns t→t|nil).
-- Ambient (word): cat flatten, λ-elim, w^0→λ, w^1→w, merge adjacent equal-base
-- powers w^a·w^b→w^(a+b)  — but NOT directly under rev (preserves the concat
-- for thm216/distribution citations).
-- Ambient (num): nadd/nmul flatten + const fold + canonical order,
-- same-base npow merge, npow^0/^1 fold, numeric nsum fold.
--
-- Rules are tried BEFORE ambient at each node so that e.g. the IH can fire on
-- (w^R)^k inside a cat before merge would hide it as (w^R)^(k+1).

local nf  -- fwd

local function rank(t)
    local r = {num=1,nvar=2,nmul=3,npow=4,nsum=5,fapp=6,
               lam=7,lit=8,lvar=9,var=10,cat=11,rev=12,pow=13,hole=14}
    return r[t.k] or 99
end
local function canon_key(t) return rank(t)*1e6 + #show(t)*100 + 0 end
local function sort_canon(ts)
    table.sort(ts, function(a,b)
        local ra,rb=rank(a),rank(b)
        if ra~=rb then return ra<rb end
        return show(a)<show(b)
    end)
end

local function ambient(t, no_merge)
    if t.k=="pow" then
        if t.e.k=="num" and t.e.n==0 then return M.LAM end
        if t.e.k=="num" and t.e.n==1 then return t.b end
    end
    if t.k=="cat" and not no_merge then
        local p=t.parts
        local out={}; local changed=false
        local function bof(x)
            if x.k=="pow" then return x.b, x.e end
            return x, M.num(1)
        end
        local i=1
        while i<=#p do
            local b,e=bof(p[i]); local j=i
            while j+1<=#p do
                local b2,e2=bof(p[j+1])
                if not t_eq(b,b2) then break end
                e=M.nadd{e,e2}; j=j+1; changed=true
            end
            e=nf(e,{})       -- normalize exponent arithmetic
            out[#out+1]=(e.k=="num" and e.n==1) and b or M.pow(b,e)
            i=j+1
        end
        if changed then return (#out==1) and out[1] or M.cat(out) end
    end
    if t.k=="npow" then
        if t.e.k=="num" then
            if t.e.n==0 then return M.num(1) end
            if t.e.n==1 then return t.b end
        end
        if t.b.k=="num" and t.e.k=="num" then return M.num(t.b.n^t.e.n) end
        if t.b.k=="npow" then return M.npow(t.b.b, M.nmul{t.b.e,t.e}) end
    end
end

local function canon_numlist(ts, zero_annihilates)  -- for nadd/nmul
    local flat = {}
    local op = zero_annihilates and "mul" or "add"
    local consts = zero_annihilates and 1 or 0
    for _,x in ipairs(ts) do
        if x.k=="nadd" and op=="add" then
            for _,y in ipairs(x.ts) do flat[#flat+1]=y end
        elseif x.k=="nmul" and op=="mul" then
            for _,y in ipairs(x.ts) do flat[#flat+1]=y end
        elseif x.k=="num" then
            consts = (op=="add") and consts + x.n or consts * x.n
        else flat[#flat+1]=x end
    end
    return flat, consts
end

nf = function(t, rs, no_merge, d)
    d = d or 0
    if d>120 then error("normalization did not terminate",0) end
    -- children first
    if t.k=="rev" then t=M.rev(nf(t.t,rs,true,d+1))
    elseif t.k=="pow" then t=M.pow(nf(t.b,rs,false,d+1), nf(t.e,rs,false,d+1))
    elseif t.k=="cat" then
        local p={}
        for _,x in ipairs(t.parts) do p[#p+1]=nf(x,rs,false,d+1) end
        t=M.cat(p)
    elseif t.k=="nadd" then
        local p={}
        for _,x in ipairs(t.ts) do p[#p+1]=nf(x,rs,false,d+1) end
        local flat,c = canon_numlist(p,false)
        if c~=0 then flat[#flat+1]=M.num(c) end
        if #flat==0 then return M.num(0) end
        sort_canon(flat)
        t = (#flat==1) and flat[1] or M.nadd(flat)
    elseif t.k=="nmul" then
        local p={}
        for _,x in ipairs(t.ts) do p[#p+1]=nf(x,rs,false,d+1) end
        local flat,c = canon_numlist(p,true)
        if c==0 then return M.num(0) end
        -- merge same-base powers:  b^e1 · b^e2 -> b^(e1+e2)  (nvar counts as ^1)
        local merged, out = {}, {}
        local function bof(x)
            if x.k=="npow" then return x.b, x.e end
            return x, M.num(1)
        end
        for _,x in ipairs(flat) do
            local b,e=bof(x)
            local key=show(b)
            if merged[key] then
                merged[key].e = M.nadd{merged[key].e, e}
            else
                local cell={b=b,e=e}; merged[key]=cell; out[#out+1]=cell
            end
        end
        flat={}
        for _,cell in ipairs(out) do
            local e=nf(cell.e,{},false,d+1)
            if not (e.k=="num" and e.n==0) then
                flat[#flat+1]=(e.k=="num" and e.n==1) and cell.b or M.npow(cell.b,e)
            end
        end
        if c~=1 then flat[#flat+1]=M.num(c) end
        if #flat==0 then return M.num(1) end
        sort_canon(flat)
        t=(#flat==1) and flat[1] or M.nmul(flat)
    elseif t.k=="npow" then t=M.npow(nf(t.b,rs,false,d+1), nf(t.e,rs,false,d+1))
    elseif t.k=="nsum" then
        t=M.nsum(t.v, nf(t.lo,rs,false,d+1), nf(t.hi,rs,false,d+1), nf(t.body,rs,false,d+1))
        if t.lo.k=="num" and t.hi.k=="num" then
            if t.hi.n < t.lo.n then return M.num(0) end
            if t.hi.n==t.lo.n then
                return nf(subst(t.body, t.v, t.lo), rs, false, d+1)
            end
        end
    elseif t.k=="fapp" then t=M.fapp(t.fn, nf(t.arg,rs,false,d+1))
    end
    -- rules first, then ambient
    for _,r in ipairs(rs) do
        local u=r(t)
        if u then return nf(u,rs,false,d+1) end
    end
    local a=ambient(t,no_merge)
    if a then return nf(a,rs,false,d+1) end
    return t
end
M.nf = nf

-- ============ bounded definition expansion (def ^i / ^) ============
-- w^(k+1) -> w^k·w and w·w^k ; likewise num npow.  Not a fixpoint rule —
-- it would oscillate against the ambient power-merge — so the step checker
-- tries each single expansion position explicitly.
local function expansions(t)
    local out={}
    local function emit_exp(x, wrap)
        local e=x.e
        local function mk(e1)
            out[#out+1]=wrap(M.cat{M.pow(x.b,e1), x.b})
            out[#out+1]=wrap(M.cat{x.b, M.pow(x.b,e1)})
        end
        local function mkn(e1)
            out[#out+1]=wrap(M.nmul{M.npow(x.b,e1), x.b})
            out[#out+1]=wrap(M.nmul{x.b, M.npow(x.b,e1)})
        end
        if x.k=="pow" then
            if e.k=="nadd" then
                for j,part in ipairs(e.ts) do
                    if part.k=="num" and part.n==1 then
                        local rest={}
                        for q,y in ipairs(e.ts) do if q~=j then rest[#rest+1]=y end end
                        mk(#rest==1 and rest[1] or M.nadd(rest))
                    end
                end
            elseif e.k=="num" and e.n>0 then mk(M.num(e.n-1)) end
        elseif x.k=="npow" then
            if e.k=="nadd" then
                for j,part in ipairs(e.ts) do
                    if part.k=="num" and part.n==1 then
                        local rest={}
                        for q,y in ipairs(e.ts) do if q~=j then rest[#rest+1]=y end end
                        mkn(#rest==1 and rest[1] or M.nadd(rest))
                    end
                end
            elseif e.k=="num" and e.n>0 then mkn(M.num(e.n-1)) end
        end
    end
    local function walk(x, wrap)
        emit_exp(x, wrap)
        if x.k=="rev" then for _,v in ipairs(expansions(x.t)) do out[#out+1]=wrap(M.rev(v)) end
        elseif x.k=="pow" then for _,v in ipairs(expansions(x.b)) do out[#out+1]=wrap(M.pow(v,x.e)) end
        elseif x.k=="cat" then
            for j,y in ipairs(x.parts) do
                for _,v in ipairs(expansions(y)) do
                    local p={}
                    for q,z in ipairs(x.parts) do p[q]=(q==j and v or z) end
                    out[#out+1]=wrap(M.cat(p))
                end
            end
        elseif x.k=="npow" then for _,v in ipairs(expansions(x.b)) do out[#out+1]=wrap(M.npow(v,x.e)) end
        elseif x.k=="nadd" or x.k=="nmul" then
            for j,y in ipairs(x.ts) do
                for _,v in ipairs(expansions(y)) do
                    local p={}
                    for q,z in ipairs(x.ts) do p[q]=(q==j and v or z) end
                    out[#out+1]=wrap({k=x.k,ts=p})
                end
            end
        elseif x.k=="nsum" then
            for _,v in ipairs(expansions(x.body)) do out[#out+1]=wrap(M.nsum(x.v,x.lo,x.hi,v)) end
            for _,v in ipairs(expansions(x.hi)) do out[#out+1]=wrap(M.nsum(x.v,x.lo,v,x.body)) end
            for _,v in ipairs(expansions(x.lo)) do out[#out+1]=wrap(M.nsum(x.v,v,x.hi,x.body)) end
        elseif x.k=="fapp" then for _,v in ipairs(expansions(x.arg)) do out[#out+1]=wrap(M.fapp(x.fn,v)) end
        end
    end
    walk(t, function(u) return u end)
    return out
end
M.expansions = expansions

-- ============ one-step rule applications (bounded search) ============
-- For rules that must NOT live in nf's fixpoint set (e.g. the induction
-- hypothesis, whose two directions would ping-pong), the step checker
-- enumerates single applications at every node explicitly.

local function each_child(t, fn)
    if t.k=="rev" then
        fn(t.t, function(v) return M.rev(v) end)
    elseif t.k=="pow" then
        fn(t.b, function(v) return M.pow(v,t.e) end)
        fn(t.e, function(v) return M.pow(t.b,v) end)
    elseif t.k=="cat" then
        for j,y in ipairs(t.parts) do
            fn(y, function(v)
                local p={}; for q,z in ipairs(t.parts) do p[q]=(q==j and v or z) end
                return M.cat(p)
            end)
        end
    elseif t.k=="npow" then
        fn(t.b, function(v) return M.npow(v,t.e) end)
        fn(t.e, function(v) return M.npow(t.b,v) end)
    elseif t.k=="nadd" or t.k=="nmul" then
        for j,y in ipairs(t.ts) do
            fn(y, function(v)
                local p={}; for q,z in ipairs(t.ts) do p[q]=(q==j and v or z) end
                return {k=t.k, ts=p}
            end)
        end
    elseif t.k=="nsum" then
        fn(t.lo,   function(v) return M.nsum(t.v,v,t.hi,t.body) end)
        fn(t.hi,   function(v) return M.nsum(t.v,t.lo,v,t.body) end)
        fn(t.body, function(v) return M.nsum(t.v,t.lo,t.hi,v) end)
    elseif t.k=="fapp" then
        fn(t.arg, function(v) return M.fapp(t.fn,v) end)
    end
end
M.each_child = each_child

-- all terms obtainable by one application of rule r at some node of t
function M.applications(r, t)
    local out = {}
    local u = r(t)
    if u then out[#out+1]=u end
    each_child(t, function(c, rebuild)
        for _,v in ipairs(M.applications(r,c)) do out[#out+1]=rebuild(v) end
    end)
    return out
end

-- ============ pattern matching (for IH rules) ============
-- metas = { name → restrict_fn(term)->bool } : pat var/nvar/lvar named `name`
-- binds to a subterm iff restrict passes; other atoms match literally.
local function match(pat, t, metas, env)
    env = env or {}
    local mk = pat.k
    if (mk=="var" or mk=="nvar" or mk=="lvar") and metas[pat.s] then
        local ok = metas[pat.s](t)
        if not ok then return nil end
        if env[pat.s] then return t_eq(env[pat.s], t) and env or nil end
        env[pat.s]=t
        return env
    end
    if mk~=t.k then return nil end
    if mk=="num" then return t.n==pat.n and env or nil end
    if mk=="lam" then return env end
    if mk=="lit" or mk=="lvar" or mk=="var" or mk=="nvar" then
        return t.s==pat.s and env or nil
    end
    if mk=="rev" then return match(pat.t, t.t, metas, env) end
    if mk=="pow" or mk=="npow" then
        env=match(pat.b,t.b,metas,env); if not env then return nil end
        return match(pat.e,t.e,metas,env)
    end
    if mk=="cat" then
        if #t.parts~=#pat.parts then return nil end
        for i=1,#pat.parts do
            env=match(pat.parts[i],t.parts[i],metas,env)
            if not env then return nil end
        end
        return env
    end
    if mk=="nadd" or mk=="nmul" then
        if #t.ts~=#pat.ts then return nil end
        for i=1,#pat.ts do
            env=match(pat.ts[i],t.ts[i],metas,env)
            if not env then return nil end
        end
        return env
    end
    if mk=="nsum" then
        if t.v~=pat.v then return nil end
        env=match(pat.lo,t.lo,metas,env); if not env then return nil end
        env=match(pat.hi,t.hi,metas,env); if not env then return nil end
        return match(pat.body,t.body,metas,env)
    end
    if mk=="fapp" then
        if t.fn~=pat.fn then return nil end
        return match(pat.arg,t.arg,metas,env)
    end
    return nil
end
M.match = match

local function instantiate(t, env)
    for name,term in pairs(env) do t=subst(t,name,term) end
    return t
end

-- make a rewrite rule t→t|nil from a pattern equation lhs = rhs.
function M.rule_from_pattern(lhs, rhs, metas)
    return function(t)
        local env = match(lhs, t, metas)
        if not env then return nil end
        return instantiate(rhs, env)
    end
end

return M
