-- wordproof/tasks.lua — exercise definitions for sheet 1, exercise 1.
--
-- A task is data + a few functions:
--   spec        identifier classification for the parser
--   sigma/dom   finite instance domain for instance checking
--   cite_map    citation label -> rule fns | "IH" | "EXPAND"
--   cite_docs   citation label -> plain-text statement of the rule
--   sections    chain sections, each with rows; a row is fixed text or a
--               template containing "?" (the student's hole).
--               expect_first/expect_last declare the chain endpoints a
--               free-mode proof must span.
--   mode        "skeleton" (holes pinned) | "free" (full chain editable)
--
-- Sections may carry `bind = { varname = "u a" }`: the induction
-- decomposition w = u·a is a premise, not an identity — bound vars are
-- DERIVED in the instance domain instead of ranging freely.  In free
-- mode the student states premises themselves via the section's
-- premise field; the declared bind then does not apply.
--
-- M.sheets groups tasks for the tabbed sheet UI:
--   sheet -> exercise groups -> subtasks (a,b,c), each with a guided
--   (skeleton) and a free variant.

local T = require "wordproof.term"
local C = require "wordproof.check"
local M = { tasks = {}, order = {} }

local function parse(s, spec)
    local t = T.parse(s, spec)
    return t
end

local function def_task(t)
    -- spec list helpers
    t.spec.wvar_list = {}
    for s,_ in pairs(t.spec.wvar or {}) do t.spec.wvar_list[#t.spec.wvar_list+1]=s end
    table.sort(t.spec.wvar_list)
    t.spec.lvar_list = {}
    for s,_ in pairs(t.spec.lvar or {}) do t.spec.lvar_list[#t.spec.lvar_list+1]=s end
    table.sort(t.spec.lvar_list)
    t.spec.nvar_list = {}
    for s,_ in pairs(t.spec.nvar or {}) do t.spec.nvar_list[#t.spec.nvar_list+1]=s end
    table.sort(t.spec.nvar_list)
    -- parse goal + templates + section premises + endpoints
    if t.goal_str then
        local p = t.goal_str:find("=")
        t.goal_lhs = parse(t.goal_str:sub(1,p-1), t.spec)
        t.goal_rhs = parse(t.goal_str:sub(p+1), t.spec)
    end
    for _,sec in ipairs(t.sections or {}) do
        for _,row in ipairs(sec.rows) do
            if row.tmpl then
                row.tmpl_parsed = parse(row.tmpl, t.spec)
            end
        end
        if sec.bind then
            sec.bind_parsed = {}
            for v,e in pairs(sec.bind) do
                sec.bind_parsed[v] = parse(e, t.spec)
            end
        end
        if sec.expect_first then
            sec.expect_first = parse(sec.expect_first, t.spec)
        end
        if sec.expect_last then
            sec.expect_last = parse(sec.expect_last, t.spec)
        end
    end
    if t.ih_str then
        local l,r = T.parse_eq(t.ih_str, t.spec)
        t.ih_lhs, t.ih_rhs = l, r
        t.ih_fns = C.build_ih(t, l, r)
    end
    M.tasks[t.id] = t
    M.order[#M.order+1] = t.id
end

-- citable rules, shown verbatim on the page ("you may cite:")
local docs_words = {
    ["def w^n"]   = "w^0 = λ,   w^(n+1) = w^n · w",
    ["def w^R"]   = "λ^R = λ,   (u·a)^R = a·u^R",
    ["Thm 2.1.6"] = "(u·v)^R = v^R · u^R",
    ["a^R = a"]   = "a^R = a   (a ∈ Σ)",
    ["λ^R = λ"]   = "λ^R = λ",
    ["λ·a = a"]   = "λ·a = a,   a·λ = a",
    ["w = u·a"]   = "the premise w = u·a may be substituted",
    ["IH"]        = "the induction hypothesis",
}
local docs_num = {
    ["def f"]     = "f(0) = 1,   f(n+1) = 1 + k·f(n)",
    ["IH"]        = "the induction hypothesis",
    ["arith"]     = "arithmetic and sum algebra",
}

-- ======================================================================
-- 1.1a  (w^R)^i = (w^i)^R   — induction on i
-- ======================================================================

local spec_a = { wvar={w=true,u=true}, lvar={a=true,b=true},
                 nvar={i=true,k=true} }

local cites_a = {
    ["def w^n"]   = {"EXPAND"},
    ["def w^R"]   = {C.rules.def_R},
    ["Thm 2.1.6"] = {C.rules.thm216},
    ["a^R = a"]   = {C.rules.aR},
    ["λ^R = λ"]   = {C.rules.lamR},
    ["λ·a = a"]   = {},
    ["IH"]        = {"IH"},
    ["w = u·a"]   = {},           -- substitution line (semantic)
}

def_task{
    id = "1.1a",
    title = "Prove (w^R)^i = (w^i)^R by induction on i.",
    goal_str = "(w^R)^i = (w^i)^R",
    hint = "In the induction step, replace i by a fresh variable "
        .. "(e.g. k) and prove the claim for k+1.",
    spec = spec_a,
    sigma = {"a","b"},
    dom = {maxlen=3, nums={k={0,4}}, num_order={"k"}},
    indvar = "i", step_var = "k",
    require_ih = true,
    cite_map = cites_a,
    cite_docs = docs_words,
    cites = {"def w^n","def w^R","Thm 2.1.6","a^R = a","λ^R = λ",
             "λ·a = a","IH","w = u·a"},
    ih_str = "(w^R)^k = (w^k)^R",
    sections = {
        { label="Base case (i = 0)",
          expect_first="(w^R)^0", expect_last="(w^0)^R",
          rows = {
            { tmpl="(w^R)^0", fixed=true },
            { tmpl="?",       cite="def w^n" },       -- λ
            { tmpl="?",       cite="λ^R = λ" },       -- λ^R
            { tmpl="(w^0)^R", cite="def w^n", fixed=true },
          }},
        { label="Induction step (k → k+1)",
          expect_first="(w^R)^(k+1)", expect_last="(w^(k+1))^R",
          rows = {
            { tmpl="(w^R)^(k+1)", fixed=true },
            { tmpl="?·w^R",       cite="def w^n" },      -- (w^R)^k
            { tmpl="?·w^R",       cite="IH" },           -- (w^k)^R
            { tmpl="(w·?)^R",     cite="Thm 2.1.6" },    -- w^k
            { tmpl="(?)^R",       cite="def w^n", last=true }, -- w^(k+1)
          }},
    },
}

-- ======================================================================
-- 1.1b  (w^R)^R = w   — induction on |w|
-- ======================================================================

local spec_b = { wvar={w=true,u=true,v=true}, lvar={a=true,b=true} }

local cites_b = {
    ["def w^R"]   = {C.rules.def_R},
    ["Thm 2.1.6"] = {C.rules.thm216},
    ["a^R = a"]   = {C.rules.aR},
    ["λ^R = λ"]   = {C.rules.lamR},
    ["λ·a = a"]   = {},
    ["IH"]        = {"IH"},
    ["w = u·a"]   = {},
}

def_task{
    id = "1.1b",
    title = "Prove (w^R)^R = w by induction on |w|.",
    goal_str = "(w^R)^R = w",
    hint = "In the induction step, decompose w = u·a with a ∈ Σ "
        .. "and apply the IH to u.  You may first prove the "
        .. "auxiliary claim a^R = a (optional section).",
    spec = spec_b,
    sigma = {"a","b"},
    dom = {maxlen=3},
    small_vars = {u=true, v=true},   -- IH may only fire on the split-off part
    require_ih = true,
    cite_map = cites_b,
    cite_docs = docs_words,
    cites = {"def w^R","Thm 2.1.6","a^R = a","λ^R = λ",
             "λ·a = a","IH","w = u·a"},
    ih_str = "(u^R)^R = u",
    sections = {
        { label="Auxiliary claim: a^R = a  (a ∈ Σ)", optional=true,
          expect_first="a^R", expect_last="a",
          rows = {
            { tmpl="a^R",       fixed=true },
            { tmpl="(?·a)^R",   cite="λ·a = a" },   -- λ
            { tmpl="a·?",       cite="def w^R" },   -- λ^R
            { tmpl="a·?",       cite="λ^R = λ" },   -- λ
            { tmpl="a",         fixed=true },
          }},
        { label="Base case (|w| = 0)",
          bind = { w = "λ" },
          expect_first="(w^R)^R", expect_last="λ",
          rows = {
            { tmpl="(w^R)^R",   fixed=true },
            { tmpl="?",         cite="λ^R = λ" },   -- λ^R
            { tmpl="?",         cite="λ^R = λ" },   -- λ
          }},
        { label="Induction step (w = u·a)",
          bind = { w = "u a" },
          expect_first="(w^R)^R", expect_last="w",
          rows = {
            { tmpl="(w^R)^R",   fixed=true },
            { tmpl="((?)^R)^R", cite="w = u·a" },   -- ua
            { tmpl="(?·u^R)^R", cite="Thm 2.1.6" }, -- a^R
            { tmpl="(a·?)^R",   cite="a^R = a" },   -- u^R
            { tmpl="?·a^R",     cite="Thm 2.1.6" }, -- (u^R)^R
            { tmpl="u·?",       cite="IH" },        -- a^R
            { tmpl="u·?",       cite="a^R = a" },   -- a
            { tmpl="w",         fixed=true, last=true },
          }},
    },
}

-- ======================================================================
-- 1.1c  f(n) = Σ_{i=0}^n k^i  — induction on n
-- ======================================================================

local spec_c = { nvar={i=true,k=true,n=true}, fns={f=true} }

-- f counts words of length <= n over a k-letter alphabet: f(0)=1,
-- f(n+1)=1+k·f(n).  Concrete evaluation for the instance check:
local function f_eval(name, n, nums)
    local acc = 1
    for _=1,n do acc = 1 + nums.k * acc end
    return acc
end

-- the recursive definition as a citable rewrite:
-- f(0) -> 1 ;  f(n+1) -> 1 + k·f(n)
local function fdef(t)
    if t.k~="fapp" then return nil end
    if t.arg.k=="num" and t.arg.n==0 then return T.num(1) end
    if t.arg.k=="nadd" then
        local rest, found = {}, false
        for _,x in ipairs(t.arg.ts) do
            if x.k=="num" and x.n==1 and not found then found=true
            else rest[#rest+1]=x end
        end
        if found then
            local inner = #rest==1 and rest[1] or T.nadd(rest)
            return T.nadd{T.num(1), T.nmul{T.nvar"k", T.fapp("f", inner)}}
        end
    end
end

local cites_c = {
    ["def f"]   = {fdef},
    ["IH"]      = {"IH"},
    ["arith"]   = C.rule_bundles.arith,
}

def_task{
    id = "1.1c",
    title = "f(n) = #{w : |w| ≤ n} over a k-letter alphabet. "
         .. "Prove f(n) = Σ_{i=0}^n k^i by induction on n.",
    goal_str = "f(n) = sum(i,0,n;k^i)",
    spec = spec_c,
    sigma = {"a","b"},      -- unused (no word vars)
    dom = {maxlen=0, nums={n={0,4}, k={1,4}}, num_order={"n","k"}},
    indvar = "n", step_var = "n",
    require_ih = true,
    cite_map = cites_c,
    cite_docs = docs_num,
    cites = {"def f","IH","arith"},
    ih_str = "f(n) = sum(i,0,n;k^i)",
    f_eval = f_eval,
    sections = {
        { label="Base case (n = 0)",
          bind = { n = "0" },
          expect_first="f(0)", expect_last="sum(i,0,0;k^i)",
          rows = {
            { tmpl="f(0)",             fixed=true },
            { tmpl="?",                cite="def f" },    -- 1
            { tmpl="?",                cite="arith" },    -- k^0
            { tmpl="sum(i,0,0;k^i)",   cite="arith", fixed=true },
          }},
        { label="Induction step (n → n+1)",
          expect_first="f(n+1)", expect_last="sum(i,0,n+1;k^i)",
          rows = {
            { tmpl="f(n+1)",              fixed=true },
            { tmpl="1 + k·?",             cite="def f" },  -- f(n)
            { tmpl="1 + k·?",             cite="IH" },     -- sum(i,0,n;k^i)
            { tmpl="1 + ?",               cite="arith" },  -- sum(i,0,n;k^(i+1))
            { tmpl="? + sum(i,1,n+1;k^i)",cite="arith" },  -- k^0
            { tmpl="sum(i,0,n+1;k^i)",    cite="arith", fixed=true, last=true },
          }},
    },
}

-- ======================================================================
-- free-mode variants: same tasks, the chain itself becomes editable.
-- The section data (labels, premises, endpoints) is kept — free blocks
-- inherit it so the checker knows where each chain must start and end.
-- ======================================================================

local function free_variant(task)
    local v = {}
    for k,x in pairs(task) do v[k]=x end
    v.id = task.id .. "-free"
    v.free = true
    v.variant_of = task.id
    return v
end

for _,id in ipairs({"1.1a","1.1b","1.1c"}) do
    local v = free_variant(M.tasks[id])
    M.tasks[v.id] = v
    M.order[#M.order+1] = v.id
end

-- ============ sheet structure for the tabbed page ============
-- sheets -> exercise groups -> subtasks (each with a guided and a
-- free variant).  Adding tasks: extend def_task above and list them
-- in the group's subtasks.
M.sheets = {
    { id="sheet1", title="Sheet 1",
      groups = {
        { id="1.1", title="Exercise 1.1",
          subtasks = {"1.1a","1.1b","1.1c"} },
      }},
}

-- flat task list for the worker's "tasks" message
function M.sheet_structure()
    local out = {}
    for _,sh in ipairs(M.sheets) do
        local groups = {}
        for _,g in ipairs(sh.groups or {}) do
            local subs = {}
            for _,sid in ipairs(g.subtasks) do
                local t = M.tasks[sid]
                local free = M.tasks[sid.."-free"]
                subs[#subs+1] = {
                    id = sid,
                    free_id = free and free.id or nil,
                    sub = sid:match("(%a)$") or sid,
                    title = t and t.title or sid,
                    goal_html = t and t.goal_lhs and
                        T.show_html(t.goal_lhs).." = "..T.show_html(t.goal_rhs)
                        or nil,
                }
            end
            groups[#groups+1] = { id=g.id, title=g.title, subtasks=subs }
        end
        out[#out+1] = { id=sh.id, title=sh.title, groups=groups }
    end
    return out
end

-- ============ serializable view for the GUI ============
function M.view(task)
    local secs, sec_labels = nil, {}
    for si,sec in ipairs(task.sections or {}) do
        sec_labels[#sec_labels+1] = { label=sec.label,
                                      optional = sec.optional or false }
        if not task.free then
            local rows = {}
            for _,r in ipairs(sec.rows) do
                rows[#rows+1] = {
                    fixed = r.fixed and T.show_html(r.tmpl_parsed) or nil,
                    tmpl_html = r.tmpl_parsed and T.show_html(r.tmpl_parsed) or nil,
                    hole = not not (r.tmpl and r.tmpl:find("%?")),
                    cite = r.cite,
                }
            end
            local binds = {}
            if sec.bind then
                for v,e in pairs(sec.bind) do
                    binds[#binds+1]=v.." = "..e
                end
            end
            secs = secs or {}
            secs[#secs+1] = { label=sec.label, rows=rows,
                              bind=table.concat(binds,", ") }
        end
    end
    local cite_docs = {}
    for _,c in ipairs(task.cites or {}) do
        cite_docs[#cite_docs+1] = { label=c,
                                    doc=(task.cite_docs or {})[c] }
    end
    return {
        id=task.id, title=task.title,
        goal = task.goal_str,
        goal_html = task.goal_lhs and
            T.show_html(task.goal_lhs).." = "..T.show_html(task.goal_rhs) or nil,
        hint = task.hint,
        cites = task.cites,
        cite_docs = cite_docs,
        ih = task.ih_str,
        free = task.free or false,
        indvar = task.indvar,
        step_var = task.step_var,
        sections = secs,
        sec_labels = sec_labels,
    }
end

return M
