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
    if t.type == "regexp" or t.type == "parts" then
        M.tasks[t.id] = t
        M.order[#M.order+1] = t.id
        return
    end
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
    id = "1.1a", letter = "A",
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
    id = "1.1b", letter = "B",
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
    id = "1.1c", letter = "C",
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
-- 1.2  regular expressions — student input is a single regexp; the
--      checker compares its language with the reference (type="regexp")
-- ======================================================================

local function regexp_task(t)
    t.type = "regexp"
    def_task(t)
end

regexp_task{
    id = "1.2a", letter = "D",
    title = "a before b before c",
    desc = "L is the language of all words over {a, b, c} in which "
        .. "all occurrences of a precede all occurrences of b and c, "
        .. "and in turn all the b precede all the c.",
    reference = "a*b*c*",
}

regexp_task{
    id = "1.2b", letter = "E",
    title = "a before b before c, nonempty",
    desc = "L is the same language as in (a), except it does not "
        .. "contain λ.",
    reference = "a+b*c*|a*b+c*|a*b*c+",
}

regexp_task{
    id = "1.2c", letter = "F",
    title = "length three",
    desc = "L is the language of all words over {a, b, c} of "
        .. "length three.",
    reference = "(a|b|c)^3",
}

regexp_task{
    id = "1.2d", letter = "G",
    title = "substring ab, length > 2",
    desc = "L is the language of all words in {a, b}* that contain "
        .. "the substring ab and have length > 2.",
    reference = "(a|b)*ab(a|b)+|(a|b)+ab",
}

regexp_task{
    id = "1.2e", letter = "H",
    title = "substrings aa and bb",
    desc = "L is the language over {a, b} such that all words contain "
        .. "both aa and bb.",
    reference = "(a|b)*aa(a|b)*bb(a|b)*|(a|b)*bb(a|b)*aa(a|b)*",
}

regexp_task{
    id = "1.2f", letter = "I",
    title = "(extra) substrings ab and ba",
    desc = "L is the language over {a, b} such that all words contain "
        .. "both ab and ba.",
    reference = "(a|b)*ab(a|b)*ba(a|b)*|(a|b)*ba(a|b)*ab(a|b)*"
             .. "|(a|b)*aba(a|b)*|(a|b)*bab(a|b)*",
}

-- ======================================================================
-- 1.3  deterministic finite automata — composite "parts" tasks:
--      a subtask bundles lettered sub-parts (a)(b)(c)… of different
--      kinds: aut (graph editor), table (transition table), trace
--      (run state sequences), accept (word acceptance), regexp.
--      task.given renders the fixed problem data above the parts.
-- ======================================================================

local function parts_task(t)
    t.type = "parts"
    -- a simplify slot whose stage is never embedded as a component by
    -- a later step is the last step: its result needs no composable
    -- form (nothing consumes it), so non-composable only warns
    local consumed = {}
    for _,p in ipairs(t.parts or {}) do
        for _,s in ipairs(p.seeds_locked or {}) do
            consumed[s:gsub("#.*","")] = true
        end
    end
    for _,p in ipairs(t.parts or {}) do
        if p.takeover_from then
            p.last_step = not consumed[p.takeover_from]
        end
    end
    def_task(t)
end

-- J (book 5.1): the transition table is given, everything else is asked
local J_DFA = "({q0,q1,q2},{a,b},"
    .. "{(q0,a,q0),(q0,b,q1),(q1,a,q2),(q1,b,q1),(q2,a,q2),(q2,b,q0)},"
    .. "q0,{q2})"

parts_task{
    id = "1.3j", letter = "J",
    title = "DFA given by transition table",
    desc = "Let M be the DFA with Q = {q0, q1, q2}, initial state q0, "
        .. "Σ = {a, b} and F = {q2}, with δ given by the table below.",
    given = { kind="table", dfa=J_DFA },
    parts = {
        { kind="aut", label="Draw the state diagram for M.",
          aut_type="dfa", alphabet="a,b", reference=J_DFA },
        { kind="trace",
          label="Trace the computations of M (the state sequence of "
             .. "the run) on each of the following words:",
          words={"abaa","bbbabb","bababa","bbbaa"}, reference=J_DFA },
        { kind="accept",
          label="Which of the four words are accepted by M?",
          words={"abaa","bbbabb","bababa","bbbaa"}, reference=J_DFA },
        { kind="regexp", label="Give a regular expression for L(M).",
          reference="a*b+a+(b a*b+a+)*" },
    },
}

-- K (book 5.3): the state diagram is given (readonly editor), the
-- transition table is asked
local K_DFA = "({q0,q1,q2},{a,b},"
    .. "{(q0,a,q1),(q0,b,q0),(q1,a,q1),(q1,b,q2),(q2,a,q0),(q2,b,q1)},"
    .. "q0,{q2})"
local K_MODEL = {
    type="dfa", alphabet="a,b",
    states = {
        {id=1, name="q0", x=70,  y=90,  initial=true},
        {id=2, name="q1", x=370, y=90},
        {id=3, name="q2", x=220, y=280, accepting=true},
    },
    transitions = {
        {id=1, from=1, to=2, label="a"},
        {id=2, from=1, to=1, label="b"},
        {id=3, from=2, to=2, label="a"},
        {id=4, from=2, to=3, label="b"},
        {id=5, from=3, to=2, label="b"},
        {id=6, from=3, to=1, label="a"},
    },
}

parts_task{
    id = "1.3k", letter = "K",
    title = "DFA given by state diagram",
    desc = "Let M be the DFA defined by the following state diagram:",
    given = { kind="aut", model=K_MODEL, readonly=true,
              alphabet="a,b", aut_type="dfa" },
    parts = {
        { kind="table",
          label="Construct the transition table of M.",
          reference=K_DFA,
          states={"q0","q1","q2"}, alphabet={"a","b"},
          initial="q0", accepting={"q2"} },
        { kind="accept",
          label="Which of the following words are accepted by M?",
          words={"baba","baab","abab","abaaab"}, reference=K_DFA },
        { kind="regexp", label="Give a regular expression for L(M).",
          reference="b*a+b(a b*a+b|b a*b)*" },
    },
}

-- L (book 5.7/5.8/5.15): draw a DFA per language; a regexp is optional
local LA_DFA = "({q0,q1,q2,q3,q4},{a,b},{(q0,a,q1),(q0,b,q4),"
    .. "(q1,a,q2),(q1,b,q4),(q2,a,q3),(q2,b,q4),(q3,a,q3),(q3,b,q3),"
    .. "(q4,a,q4),(q4,b,q4)},q0,{q0,q1,q2,q4})"
local LB_DFA = "({q0,q1,q2,q3},{a,b},{(q0,a,q1),(q0,b,q0),"
    .. "(q1,a,q2),(q1,b,q0),(q2,a,q3),(q2,b,q0),(q3,a,q3),(q3,b,q3)},"
    .. "q0,{q0,q1,q2})"
local LC_DFA = "({q0,q1,q2,q3,q4},{a,b,c},"
    .. "{(q0,a,q2),(q0,b,q1),(q0,c,q1),(q1,a,q3),(q1,b,q0),(q1,c,q0),"
    .. "(q2,a,q4),(q2,b,q3),(q2,c,q3),(q3,a,q4),(q3,b,q2),(q3,c,q2),"
    .. "(q4,a,q4),(q4,b,q4),(q4,c,q4)},q0,{q3})"

parts_task{
    id = "1.3l", letter = "L",
    title = "Draw a DFA for each language",
    desc = "For each of the following languages L, draw the state "
        .. "diagram of a DFA that accepts L.  The regular expression "
        .. "is optional.",
    parts = {
        { kind="aut", with_regexp=true, aut_type="dfa", alphabet="a,b",
          label="L: words over {a, b} that do not begin with aaa.",
          reference=LA_DFA,
          re_reference="(λ|a|aa)(λ|b(a|b)*)" },
        { kind="aut", with_regexp=true, aut_type="dfa", alphabet="a,b",
          label="L: words over {a, b} that do not contain the "
             .. "substring aaa.",
          reference=LB_DFA,
          re_reference="(λ|a|aa)(b+(λ|a|aa))*" },
        { kind="aut", with_regexp=true, aut_type="dfa",
          alphabet="a,b,c",
          label="(extra) L: words of even length over {a, b, c} "
             .. "that contain exactly one a.",
          reference=LC_DFA,
          re_reference="((b|c)(b|c))*(a(b|c)|(b|c)a)((b|c)(b|c))*" },
    },
}

-- ======================================================================
-- Sheet 2
-- ======================================================================

-- 2.1  RE -> DFA by hand: the reference DFAs are the model solutions
--      from the exercise sheet (dead state qe included; the checker
--      reports a warning for extra states, not an error)
local R21a_DFA = "({q0,q1,q2,q3,qe},{a,b},"
    .. "{(q0,a,q1),(q0,b,q2),(q1,a,qe),(q1,b,q0),(q2,a,q3),(q2,b,qe),"
    .. "(q3,a,qe),(q3,b,qe),(qe,a,qe),(qe,b,qe)},q0,{q3})"      -- (ab)*ba
local R21b_DFA = "({q0,q1,qe},{a,b},"
    .. "{(q0,a,q1),(q0,b,qe),(q1,a,q0),(q1,b,q1),"
    .. "(qe,a,qe),(qe,b,qe)},q0,{q0})"                          -- (ab*a)*
local R21c_DFA = "({q0,q1,q2,q3,qe},{a,b},"
    .. "{(q0,a,q1),(q0,b,qe),(q1,a,q2),(q1,b,qe),(q2,a,q1),(q2,b,q3),"
    .. "(q3,a,qe),(q3,b,q0),(qe,a,qe),(qe,b,qe)},q0,{q0})"      -- ((aa)+bb)*
local R21d_DFA = "({q0,q1,q2,q3,q4,q5,qe},{a,b},"
    .. "{(q0,a,q1),(q0,b,qe),(q1,a,q2),(q1,b,qe),(q2,a,q3),(q2,b,q3),"
    .. "(q3,a,q3),(q3,b,q4),(q4,a,q3),(q4,b,q5),(q5,a,q3),(q5,b,q5),"
    .. "(qe,a,qe),(qe,b,qe)},q0,{q5})"                          -- aa(a|b)+bb

parts_task{
    id = "2.1m", letter = "M",
    title = "Construct DFA from RE",
    desc = "For each of the following regular expressions E, draw the "
        .. "state diagram of a DFA that accepts L(E).",
    parts = {
        { kind="aut", aut_type="dfa", alphabet="a,b",
          label="E = (ab)*ba", reference=R21a_DFA },
        { kind="aut", aut_type="dfa", alphabet="a,b",
          label="E = (ab*a)*", reference=R21b_DFA },
        { kind="aut", aut_type="dfa", alphabet="a,b",
          label="E = ((aa)+bb)*", reference=R21c_DFA },
        { kind="aut", aut_type="dfa", alphabet="a,b",
          label="E = aa(a∪b)+bb", reference=R21d_DFA },
    },
}

-- ======================================================================
-- 2.2  RE -> NFA-lambda, STEPWISE: each part is an NFA-λ construction
--      checked against its own sub-expression; `seeds` lists earlier
--      parts whose automaton can be inserted into this part's editor,
--      so composition happens visibly on the canvas (insert dropdown).
-- ======================================================================

local function nfa_step(label, reference, seeds, alphabet)
    return { kind="aut", aut_type="nfa-eps",
             alphabet=alphabet or "a,b",
             label=label, reference=reference, seeds=seeds }
end

parts_task{
    id = "2.2n", letter = "N",
    variants = { {id="2.2n", label="free form"},
                 {id="2.2n-g", label="guided"} },
    title = "From RE to NFA-λ: (ab)* ∪ a*",
    desc = "Use the construction from the lecture to derive the state "
        .. "diagram of an NFA-λ that accepts L(E), where "
        .. "E = (ab)* ∪ a*.  Build it step by step: each part asks for "
        .. "an intermediate automaton, and the 'insert' dropdown of a "
        .. "part lets you place a copy of an earlier part's automaton "
        .. "on the canvas to compose it further.  You may omit "
        .. "obviously unnecessary λ-steps.",
    parts = {
        nfa_step("E = a", "a"),
        nfa_step("E = b", "b"),
        nfa_step("E = ab — from the NFAs for a and b "
            .. "(insert both, then connect)", "ab", {1,2}),
        nfa_step("E = (ab)* — from the NFA for ab", "(ab)*", {3}),
        nfa_step("E = a* — from the NFA for a", "a*", {1}),
        nfa_step("E = (ab)* ∪ a* — from the NFAs for (ab)* and a*",
                 "(ab)*|a*", {4,5}),
    },
}

parts_task{
    id = "2.2o", letter = "O",
    variants = { {id="2.2o", label="free form"},
                 {id="2.2o-g", label="guided"} },
    title = "From RE to NFA-λ: (abc)*a*",
    desc = "The same stepwise construction for "
        .. "E = (abc)* ∪ a* over {a, b, c}.",
    parts = {
        nfa_step("E = a", "a", nil, "a,b,c"),
        nfa_step("E = b", "b", nil, "a,b,c"),
        nfa_step("E = c", "c", nil, "a,b,c"),
        nfa_step("E = ab — from the NFAs for a and b", "ab",
                 {1,2}, "a,b,c"),
        nfa_step("E = abc — from the NFAs for ab and c", "abc",
                 {4,3}, "a,b,c"),
        nfa_step("E = (abc)* — from the NFA for abc", "(abc)*",
                 {5}, "a,b,c"),
        nfa_step("E = a* — from the NFA for a", "a*",
                 {1}, "a,b,c"),
        nfa_step("E = (abc)* ∪ a* — from the NFAs for (abc)* and a*",
                 "(abc)*|a*", {6,7}, "a,b,c"),
    },
}

parts_task{
    id = "2.2p", letter = "P",
    variants = { {id="2.2p", label="free form"},
                 {id="2.2p-g", label="guided"} },
    title = "(extra) From RE to NFA-λ: (ba∪bb)* ∪ (ab∪aa)*",
    desc = "(extra) The same stepwise construction for "
        .. "E = (ba ∪ bb)* ∪ (ab ∪ aa)*.",
    parts = {
        nfa_step("E = a", "a"),
        nfa_step("E = b", "b"),
        nfa_step("E = ba — from the NFAs for b and a", "ba", {2,1}),
        nfa_step("E = bb — from the NFA for b (insert twice)", "bb", {2}),
        nfa_step("E = ba ∪ bb — from the NFAs for ba and bb",
                 "ba|bb", {3,4}),
        nfa_step("E = (ba ∪ bb)* — from the NFA for ba ∪ bb",
                 "(ba|bb)*", {5}),
        nfa_step("E = ab — from the NFAs for a and b", "ab", {1,2}),
        nfa_step("E = aa — from the NFA for a (insert twice)", "aa", {1}),
        nfa_step("E = ab ∪ aa — from the NFAs for ab and aa",
                 "ab|aa", {7,8}),
        nfa_step("E = (ab ∪ aa)* — from the NFA for ab ∪ aa",
                 "(ab|aa)*", {9}),
        nfa_step("E = (ba ∪ bb)* ∪ (ab ∪ aa)* — from the two "
            .. "*-constructions", "(ba|bb)*|(ab|aa)*", {6,10}),
    },
}

-- ----------------------------------------------------------------------
-- guided variants: same construction chain, but the components from
-- previous steps are GIVEN — embedded as locked, visually distinct
-- subgraphs (refresh-components button re-syncs them).  Composition is
-- checked structurally: the embedded parts must be present verbatim
-- and wired into the automaton (check="compose").  Each composition
-- step is followed by an optional simplify slot whose content — taken
-- over from the compose editor, then reduced by hand — becomes the
-- effective automaton the next step embeds.

local function gstep(sid, label, reference, seeds, alphabet)
    return { kind="aut", aut_type="nfa-eps",
             alphabet=alphabet or "a,b",
             label=label, reference=reference, sub=sid .. ")",
             sid=sid, seeds_locked=seeds,
             -- atoms have no components to embed, but compose still
             -- runs the composable-form check: a stage only counts
             -- when it can serve as a later component
             check = "compose" }
end

local function sstep(sid, reference, alphabet)
    return { kind="aut", aut_type="nfa-eps",
             alphabet=alphabet or "a,b",
             label="optional: simplify — 'take over' adopts the "
                .. "automaton above; simplify it by hand",
             sub=sid .. "')",
             takeover_from=sid, reference=reference, optional=true }
end

parts_task{
    id = "2.2n-g", letter = "N",
    title = "From RE to NFA-λ: (ab)* ∪ a*",
    desc = "Guided variant: each composition step embeds the automata "
        .. "of the earlier steps as locked components (the navy "
        .. "parts) — wire them together with your own states and "
        .. "transitions, entering each component via its initial "
        .. "state and leaving it via its final state, so the result "
        .. "stays composable.  The components stay in sync with the "
        .. "earlier steps automatically; an optional simplify slot "
        .. "lets you reduce a step's automaton, and the simplified "
        .. "version is what the next step embeds.",
    parts = {
        gstep("a", "E = a", "a"),
        gstep("b", "E = b", "b"),
        gstep("ab", "E = ab — compose the given components", "ab",
              {"a","b"}),
        sstep("ab", "ab"),
        gstep("abS", "E = (ab)* — compose on the given component",
              "(ab)*", {"ab"}),
        sstep("abS", "(ab)*"),
        gstep("aS", "E = a* — compose on the given component", "a*",
              {"a"}),
        sstep("aS", "a*"),
        gstep("u", "E = (ab)* ∪ a* — compose the two components",
              "(ab)*|a*", {"abS","aS"}),
        sstep("u", "(ab)*|a*"),
    },
}

parts_task{
    id = "2.2o-g", letter = "O",
    title = "From RE to NFA-λ: (abc)*a*",
    desc = "Guided variant for E = (abc)* ∪ a* over {a, b, c} — "
        .. "locked components from the previous steps, entered via "
        .. "their initial and left via their final state; optional "
        .. "simplify slots feed the next step.",
    parts = {
        gstep("a", "E = a", "a", nil, "a,b,c"),
        gstep("b", "E = b", "b", nil, "a,b,c"),
        gstep("c", "E = c", "c", nil, "a,b,c"),
        gstep("ab", "E = ab — compose the given components", "ab",
              {"a","b"}, "a,b,c"),
        sstep("ab", "ab", "a,b,c"),
        gstep("abc", "E = abc — compose the given components", "abc",
              {"ab","c"}, "a,b,c"),
        sstep("abc", "abc", "a,b,c"),
        gstep("abcS", "E = (abc)* — compose on the given component",
              "(abc)*", {"abc"}, "a,b,c"),
        sstep("abcS", "(abc)*", "a,b,c"),
        gstep("aS", "E = a* — compose on the given component", "a*",
              {"a"}, "a,b,c"),
        sstep("aS", "a*", "a,b,c"),
        gstep("u", "E = (abc)* ∪ a* — compose the two components",
              "(abc)*|a*", {"abcS","aS"}, "a,b,c"),
        sstep("u", "(abc)*|a*", "a,b,c"),
    },
}

parts_task{
    id = "2.2p-g", letter = "P",
    title = "(extra) From RE to NFA-λ: (ba∪bb)* ∪ (ab∪aa)*",
    desc = "(extra) Guided variant for E = (ba ∪ bb)* ∪ (ab ∪ aa)* — "
        .. "locked components, entered via their initial and left via "
        .. "their final state.",
    parts = {
        gstep("a", "E = a", "a"),
        gstep("b", "E = b", "b"),
        gstep("ba", "E = ba — compose the given components", "ba",
              {"b","a"}),
        sstep("ba", "ba"),
        gstep("bb", "E = bb — compose on the given component "
              .. "(embedded twice)", "bb", {"b","b#2"}),
        gstep("bab", "E = ba ∪ bb — compose the given components",
              "ba|bb", {"ba","bb"}),
        sstep("bab", "ba|bb"),
        gstep("babS", "E = (ba ∪ bb)* — compose on the given component",
              "(ba|bb)*", {"bab"}),
        sstep("babS", "(ba|bb)*"),
        gstep("ab", "E = ab — compose the given components", "ab",
              {"a","b"}),
        sstep("ab", "ab"),
        gstep("aa", "E = aa — compose on the given component "
              .. "(embedded twice)", "aa", {"a","a#2"}),
        gstep("aba", "E = ab ∪ aa — compose the given components",
              "ab|aa", {"ab","aa"}),
        sstep("aba", "ab|aa"),
        gstep("abaS", "E = (ab ∪ aa)* — compose on the given component",
              "(ab|aa)*", {"aba"}),
        sstep("abaS", "(ab|aa)*"),
        gstep("u", "E = (ba ∪ bb)* ∪ (ab ∪ aa)* — compose the two "
              .. "components", "(ba|bb)*|(ab|aa)*", {"babS","abaS"}),
        sstep("u", "(ba|bb)*|(ab|aa)*"),
    },
}

-- ======================================================================
-- 2.3  NFA -> DFA (Sudkamp 5.36): lambda-closures, input transition
--      function t (set-valued table), DFA diagram, regexp
-- ======================================================================
local Q_NFA = "({q0,q1,q2},{a,b,c},"
    .. "{(q0,a,q0),(q0,c,q1),(q0,λ,q2),(q1,c,q1),"
    .. "(q2,b,q2),(q2,b,q1)},q0,{q1,q2})"
local Q_MODEL = {
    type="nfa-eps", alphabet="a,b,c",
    states = {
        {id=1, name="q0", x=70,  y=130, initial=true},
        {id=2, name="q1", x=370, y=130, accepting=true},
        {id=3, name="q2", x=300, y=330, accepting=true},
    },
    transitions = {
        {id=1, from=1, to=1, label="a"},
        {id=2, from=1, to=2, label="c"},
        {id=3, from=1, to=3, label="λ"},
        {id=4, from=2, to=2, label="c"},
        {id=5, from=3, to=3, label="b"},
        {id=6, from=3, to=2, label="b"},
    },
}
-- subset-construction DFA (sets named S0={q0,q2}, S1={q1}, S12={q1,q2},
-- SE=∅); checked by language, so names do not matter
local Q_DFA = "({S0,S1,S12,SE},{a,b,c},"
    .. "{(S0,a,S0),(S0,b,S12),(S0,c,S1),"
    .. "(S1,a,SE),(S1,b,SE),(S1,c,S1),"
    .. "(S12,a,SE),(S12,b,S12),(S12,c,S1),"
    .. "(SE,a,SE),(SE,b,SE),(SE,c,SE)},S0,{S0,S1,S12})"

parts_task{
    id = "2.3q", letter = "Q",
    title = "Determinise an NFA-λ",
    desc = "Let M be the following NFA-λ.  Determinise it following "
        .. "the algorithm from the lecture (or Algorithm 5.6.3 in the "
        .. "Sudkamp book).",
    given = { kind="aut", model=Q_MODEL, readonly=true,
              alphabet="a,b,c", aut_type="nfa-eps" },
    parts = {
        { kind="closure",
          label="Compute the λ-closure(qi) for i = 0,1,2.",
          states={"q0","q1","q2"}, reference=Q_NFA },
        { kind="stable",
          label="Give the input transition function t for M "
             .. "(cells are state sets; ∅ for the empty set).",
          states={"q0","q1","q2"}, alphabet={"a","b","c"},
          reference=Q_NFA },
        { kind="aut", aut_type="dfa", alphabet="a,b,c",
          label="Construct a state diagram of a DFA equivalent to M.",
          reference=Q_DFA },
        { kind="regexp", label="Give a regular expression for L(M).",
          reference="a*b*c*" },
    },
}

-- (extra) the "aa twice, separately" problem: RE -> NFA -> DFA
parts_task{
    id = "2.3u", letter = "U",
    title = "(extra) aa twice, separately",
    desc = "(extra) Let L be the language of words over {a, b} in "
        .. "which the substring aa occurs at least twice separately "
        .. "(aaa ∉ L).",
    parts = {
        { kind="regexp",
          label="Give a regular expression E with L(E) = L.",
          reference="(a|b)*aa(a|b)*aa(a|b)*" },
        { kind="aut", aut_type="nfa-eps", alphabet="a,b",
          label="Draw the state diagram of an NFA (with or without "
             .. "λ-steps) that accepts L.",
          reference="(a|b)*aa(a|b)*aa(a|b)*" },
        { kind="aut", aut_type="dfa", alphabet="a,b",
          label="Determinise your automaton: draw a DFA for L.",
          reference="(a|b)*aa(a|b)*aa(a|b)*" },
    },
}

-- ======================================================================
-- 2.4  Complement: flip on a DFA (easy) vs determinise-then-flip (NFA)
-- ======================================================================
-- the 2.4a machine is Exercise 5.3 again — K_DFA/K_MODEL from sheet 1
parts_task{
    id = "2.4r", letter = "R",
    title = "Complement of a DFA",
    desc = "Construct a finite automaton that accepts the complement "
        .. "of the language accepted by the finite automaton M below "
        .. "(this is very easy).",
    given = { kind="aut", model=K_MODEL, readonly=true,
              alphabet="a,b", aut_type="dfa" },
    parts = {
        { kind="aut", aut_type="dfa", alphabet="a,b",
          label="Draw an automaton for L(M)ᶜ.",
          reference=K_DFA, complement=true },
    },
}

-- 5.23 NFA: parallel a-edges out of q0 — determinisation first
local S_NFA = "({q0,q1,q2},{a,b},"
    .. "{(q0,a,q0),(q0,a,q1),(q1,b,q1),(q1,b,q2),"
    .. "(q2,a,q1),(q2,a,q0)},q0,{q2})"
local S_MODEL = {
    type="nfa", alphabet="a,b",
    states = {
        {id=1, name="q0", x=70,  y=130, initial=true},
        {id=2, name="q1", x=370, y=130},
        {id=3, name="q2", x=300, y=330, accepting=true},
    },
    transitions = {
        {id=1, from=1, to=1, label="a"},
        {id=2, from=1, to=2, label="a"},
        {id=3, from=2, to=2, label="b"},
        {id=4, from=2, to=3, label="b"},
        {id=5, from=3, to=2, label="a"},
        {id=6, from=3, to=1, label="a"},
    },
}

parts_task{
    id = "2.4s", letter = "S",
    title = "Complement of an NFA",
    desc = "Construct a finite automaton that accepts the complement "
        .. "of the language accepted by the finite automaton M below.  "
        .. "Hint: this is not so easy — M is nondeterministic, so "
        .. "determinise first.  (Any automaton for the complement "
        .. "language is accepted.)",
    given = { kind="aut", model=S_MODEL, readonly=true,
              alphabet="a,b", aut_type="nfa" },
    parts = {
        { kind="aut", aut_type="nfa", alphabet="a,b",
          label="Draw an automaton for L(M)ᶜ.",
          reference=S_NFA, complement=true },
    },
}

-- ======================================================================
-- 2.5  NFA -> RE (state elimination): the 5.23 machine again
-- ======================================================================
parts_task{
    id = "2.5t", letter = "T",
    title = "From NFA to regular expression",
    desc = "Use the algorithm from the lecture (state elimination) to "
        .. "obtain a regular expression for the language accepted by "
        .. "the following automaton.",
    given = { kind="aut", model=S_MODEL, readonly=true,
              alphabet="a,b", aut_type="nfa" },
    parts = {
        { kind="regexp",
          label="Give a regular expression for L(M).",
          reference="a*ab*b(aa*ab*b|ab*b)*" },
    },
}

-- ======================================================================
-- SHEET 3 — pumping lemma, closure properties, DFA minimisation
-- ======================================================================

-- ---------- 3.1: the pumping adversary game ----------
-- kind="pumping": the student picks z(k) as a k-pattern, the system
-- instantiates at k=3 and enumerates all decompositions |uv|≤k,
-- |v|≥1; each split needs an i with uv^iw ∉ L.

local function pstep(sub, lang, label)
    return { kind="pumping", sub=sub, lang=lang, label=label }
end

parts_task{
    id = "3.1p", letter = "P",
    title = "Pumping lemma: proving non-regularity",
    desc = "Play the adversary role of the pumping proof yourself: "
        .. "first give a word z(k) that is in L and at least k long "
        .. "for EVERY k (write e.g. a^k b^k — a^{k+1}, a^{2k}, a^3 "
        .. "work too).  'decompose' then lists every legal split "
        .. "z = uvw with |uv| ≤ k and |v| ≥ 1 for k = 3 — pick a "
        .. "pumping index i for EACH split so that uv^iw leaves L "
        .. "(you can redo the example at other values of k).  Then "
        .. "write the GENERAL decomposition yourself: u, v, w as "
        .. "patterns in k and your own parameters — every legal "
        .. "split has u = sym^p, v = sym^q with p ≥ 0, q ≥ 1 and "
        .. "p+q ≤ k — plus a pumping index i(k,q).  The checker "
        .. "verifies uvw ≡ z(k), legality, coverage of every legal "
        .. "split, and uv^iw ∉ L — symbolically for all k ≥ 1 when "
        .. "it can, sampled otherwise.",
    parts = {
        pstep("a)", "eq_ab",
              "L = {w ∈ {a,b}* | #a(w) = #b(w)}"),
        pstep("b)", "parens",
              "L = matched parentheses over {(,)}"),
        pstep("c)", "pal",
              "L = palindromes over {a,b}"),
        pstep("d)", "ww",
              "L = {ww | w ∈ {a,b}*}"),
        pstep("e)", "anbm_lt",
              "L = {aⁿbᵐ | n < m}   (extra)"),
        pstep("f)", "aibjc",
              "L = {aⁱbʲc²ʲ | i,j ≥ 0}   (extra)"),
        { kind="choice", sub="g)",
          label="L = {w ∈ {a,b}* | w ≠ w^R} (non-palindromes): "
             .. "which argument proves L non-regular?",
          slots = {
            { key="arg", label="proof idea",
              options = {
                { id="comp",  label="Suppose L regular. Then "
                    .. "L̄ is regular (closure under complement), "
                    .. "but L̄ is the palindromes — contradiction "
                    .. "with part c)." },
                { id="pump",  label="Direct pumping: choose "
                    .. "z = a^k b a^{k+1} ∈ L and pump with i = 2." },
                { id="incl",  label="L ⊆ {a,b}* and {a,b}* is "
                    .. "regular, so L is regular." },
                { id="fin",   label="Pumping cannot apply because "
                    .. "L is infinite." } } } },
          sel_check = function(sel)
              if sel.arg == "comp" then
                  return { ok=true, kind="ok",
                           msg="closure under complement + the "
                            .. "palindrome result — correct" }
              elseif sel.arg == "pump" then
                  return { ok=false, kind="fail",
                    msg="z = a^k b a^{k+1} cannot be beaten: pumping "
                     .. "the a-block keeps a non-palindrome "
                     .. "(#a-parts stay different) — that z does "
                     .. "not work" }
              elseif sel.arg == "incl" then
                  return { ok=false, kind="fail",
                    msg="subsets of regular languages need not be "
                     .. "regular — this proves nothing" }
              end
              return { ok=false, kind="fail",
                       msg="infinitude does not stop the pumping "
                        .. "lemma" }
          end },
    },
}

-- ---------- 3.2: closure properties ----------

-- palette of example languages with known regularity flags; used by
-- the "give examples L1, L2" questions below
local PAL = {
    sigmastar  = { label="Σ* = {a,b}*",              reg=true  },
    empty      = { label="∅",                        reg=true  },
    lam        = { label="{λ}",                      reg=true  },
    astarbstar = { label="a*b* = {aⁿbᵐ}",            reg=true  },
    abs        = { label="(ab)* = {(ab)ⁿ}",          reg=true  },
    finab      = { label="{ab, ba}",                 reg=true  },
    aorb       = { label="a* ∪ b*",                  reg=true  },
    anbn       = { label="{aⁿbⁿ | n≥0}",             reg=false },
    anbm_ne    = { label="{aⁿbᵐ | n≠m}",             reg=false },
    anbm_lt    = { label="{aⁿbᵐ | n<m}",             reg=false },
    pal        = { label="palindromes",              reg=false },
    nonpal     = { label="non-palindromes",          reg=false },
    ww         = { label="{ww}",                     reg=false },
    comp_anbn  = { label="Σ* ∖ {aⁿbⁿ}",              reg=false },
    an2        = { label="{aⁿ²}",                    reg=false },
    a2n        = { label="{a^2ⁿ}",                   reg=false },
    aprime     = { label="{a^p | p prime}",          reg=false },
    an3        = { label="{aⁿ³}",                    reg=false },
}
local PAL_ORDER = { "sigmastar","empty","lam","astarbstar","abs",
                    "finab","aorb",
                    "anbn","anbm_ne","anbm_lt","pal","nonpal","ww",
                    "comp_anbn","an2","a2n","aprime","an3" }

local function pal_options()
    local o = {}
    for _,id in ipairs(PAL_ORDER) do
        o[#o+1] = { id=id, label=PAL[id].label }
    end
    return o
end
local function pal_slot(key, label)
    return { key=key, label=label, options=pal_options() }
end

-- regular L1 ∪ non-regular L2 stays regular only in these cases
local UNION_REG = {
    sigmastar  = "all",   -- Σ* ∪ X = Σ*
    astarbstar = { anbn=true, anbm_ne=true, anbm_lt=true },
}
-- regular L1 ∩ non-regular L2 is regular in these cases
local INTER_REG = {
    empty="all", lam="all", finab="all", abs="all",
    aorb       = { anbn=true, anbm_ne=true, anbm_lt=true,
                   pal=true, nonpal=true, ww=true,
                   comp_anbn=true },
    astarbstar = { pal=true, nonpal=true, ww=true },
}
-- non-regular ∪ non-regular can be regular (both directions listed)
local UNION_REG_NN = {
    anbn      = { anbm_ne=true, comp_anbn=true },
    anbm_ne   = { anbn=true },
    comp_anbn = { anbn=true },
    pal       = { nonpal=true },
    nonpal    = { pal=true },
}
-- non-regular L with regular L*
local STAR_REG = { an2="a* (every n is a sum of squares)",
                   a2n="a* (binary representations)",
                   aprime="a* ∖ {a} (cofinite)",
                   an3="a* (a = a^1³ ∈ L)",
                   pal="Σ* (every single letter is a palindrome)" }

local function sel_flags(sel)
    local a, b = PAL[sel.l1], PAL[sel.l2]
    if not a or not b then
        return nil, { ok=false, kind="fail",
                      msg="choose from the list" }
    end
    return a, b
end
local function in_tab(tab, x, y)
    local t = tab[x]
    if t == "all" then return true end
    return type(t) == "table" and t[y] and true or false
end

local function sc_pair(goal)
    return function(sel)
        local a, b = sel_flags(sel)
        if not a then return b end
        if goal == "ureg" then
            if not a.reg then return { ok=false, kind="fail",
                msg="L1 must be regular — " .. a.label
                 .. " is not regular" } end
            if b.reg then return { ok=false, kind="fail",
                msg="L2 must be NON-regular — " .. b.label
                 .. " is regular" } end
            if in_tab(UNION_REG, sel.l1, sel.l2) then
                return { ok=true, kind="ok",
                         msg="L1 ∪ L2 = " .. a.label
                          .. " is regular ✓" }
            end
            return { ok=false, kind="fail",
                     msg="this union is NON-regular — L1 must "
                      .. "cover the gap (hint: think big)" }
        elseif goal == "unon" then
            if not a.reg then return { ok=false, kind="fail",
                msg="L1 must be regular — " .. a.label
                 .. " is not regular" } end
            if b.reg then return { ok=false, kind="fail",
                msg="L2 must be NON-regular — " .. b.label
                 .. " is regular" } end
            if in_tab(UNION_REG, sel.l1, sel.l2) then
                return { ok=false, kind="fail",
                     msg="this union is regular — violates the "
                      .. "condition" }
            end
            return { ok=true, kind="ok",
                     msg="L1 ∪ L2 stays non-regular ✓" }
        elseif goal == "ireg" then
            if not a.reg then return { ok=false, kind="fail",
                msg="L1 must be regular — " .. a.label
                 .. " is not regular" } end
            if b.reg then return { ok=false, kind="fail",
                msg="L2 must be NON-regular — " .. b.label
                 .. " is regular" } end
            if in_tab(INTER_REG, sel.l1, sel.l2) then
                return { ok=true, kind="ok",
                         msg="L1 ∩ L2 is regular ✓" }
            end
            return { ok=false, kind="fail",
                     msg="this intersection is NON-regular — "
                      .. "pick an L1 that cuts L2 down to "
                      .. "something regular" }
        elseif goal == "nnureg" then
            if a.reg or b.reg then return { ok=false, kind="fail",
                msg="BOTH must be non-regular" } end
            if in_tab(UNION_REG_NN, sel.l1, sel.l2) then
                return { ok=true, kind="ok",
                         msg="L1 ∪ L2 is regular ✓" }
            end
            return { ok=false, kind="fail",
                     msg="this union stays non-regular — look for "
                      .. "two non-regular languages that "
                      .. "complement each other" }
        end
    end
end

parts_task{
    id = "3.2c", letter = "C",
    title = "Closure properties",
    desc = "Two closure arguments, then the constructions carried "
        .. "out on a concrete machine.",
    parts = {
        { kind="regexp", sub="a)",
          label="L' = {w ∈ L | w ends with aa}.  Give a regular "
             .. "expression Ê over {a,b,c} for the CONDITION, i.e. "
             .. "L(Ê) = Σ*aa (then L' = L ∩ L(Ê))",
          reference="(a|b|c)*aa" },
        { kind="regexp", sub="b)",
          label="L' = {w ∉ L | w has no a}.  Give Ê over {a,b,c} "
             .. "with L(Ê) = {words without a} (then L' = L̄ ∩ L(Ê))",
          reference="(b|c)*" },
        { kind="choice", sub="c)",
          label="Which closure properties prove parts a) and b)?",
          slots = {
            { key="c", label="used properties",
              options = {
                { id="inter",   label="a): ∩;  b): complement + ∩" },
                { id="un",      label="a): ∪;  b): complement + ∪" },
                { id="concat",  label="a): concatenation;  b): ∩" },
                { id="star",    label="a): star;  b): complement" } } } },
          sel_check = function(sel)
              if sel.c == "inter" then
                  return { ok=true, kind="ok",
                    msg="∩ (a) and complement + ∩ (b) — right" }
              end
              return { ok=false, kind="fail",
                       msg="think again: a) intersects L with a "
                        .. "regular condition; b) needs the "
                        .. "complement too" }
          end },
        { kind="aut", aut_type="nfa-eps", alphabet="a,b",
          sub="d)", reference="(ab)*(λ|a)",
          label="prefixes of L(M): build an NFA-λ accepting "
             .. "{u | ∃v: uv ∈ L(M)} for the given M" },
        { kind="aut", aut_type="nfa-eps", alphabet="a,b",
          sub="e)", reference="(ba)*",
          label="reversals: build an NFA-λ accepting "
             .. "{w^R | w ∈ L(M)}   (extra)" },
        { kind="aut", aut_type="nfa-eps", alphabet="a,b",
          sub="f)", reference="(a|b)*(ab)*",
          label="words having a suffix in L(M): build an NFA-λ "
             .. "accepting {uv | v ∈ L(M)} = Σ*·L(M)   (extra)" },
    },
    given = { kind="aut", model={
        type="dfa", alphabet="a,b",
        states={ {id=1,name="q0",x=120,y=140,initial=true,accepting=true},
                 {id=2,name="q1",x=300,y=140},
                 {id=3,name="q2",x=210,y=320} },
        transitions={ {id=1,from=1,to=2,label="a"},
                      {id=2,from=1,to=3,label="b"},
                      {id=3,from=2,to=3,label="a"},
                      {id=4,from=2,to=1,label="b"},
                      {id=5,from=3,to=3,label="a,b"} } },
        readonly=true, alphabet="a,b", aut_type="dfa" },
}

parts_task{
    id = "3.2e", letter = "E",
    title = "Regular and non-regular languages can mix",
    desc = "Give example languages L1, L2 over {a,b} satisfying "
        .. "each combination of conditions (choose from the "
        .. "palette).",
    parts = {
        { kind="choice", sub="a)",
          label="L1 regular, L2 non-regular, L1 ∪ L2 regular",
          slots = { pal_slot("l1","L1"), pal_slot("l2","L2") },
          sel_check = sc_pair("ureg") },
        { kind="choice", sub="b)",
          label="L1 regular, L2 non-regular, L1 ∪ L2 non-regular",
          slots = { pal_slot("l1","L1"), pal_slot("l2","L2") },
          sel_check = sc_pair("unon") },
        { kind="choice", sub="c)",
          label="L1 regular, L2 non-regular, L1 ∩ L2 regular",
          slots = { pal_slot("l1","L1"), pal_slot("l2","L2") },
          sel_check = sc_pair("ireg") },
        { kind="choice", sub="d)",
          label="L1, L2 both non-regular, L1 ∪ L2 regular",
          slots = { pal_slot("l1","L1"), pal_slot("l2","L2") },
          sel_check = sc_pair("nnureg") },
        { kind="choice", sub="e)",
          label="L1 non-regular but L1* regular   (extra)",
          slots = { pal_slot("l1","L1") },
          sel_check = function(sel)
              local a = PAL[sel.l1]
              if not a then
                  return { ok=false, kind="fail",
                           msg="choose from the list" }
              end
              if a.reg then
                  return { ok=false, kind="fail",
                           msg="L1 must be NON-regular — "
                            .. a.label .. " is regular" }
              end
              local why = STAR_REG[sel.l1]
              if why then
                  return { ok=true, kind="ok",
                           msg="L1* = " .. why .. " — regular ✓" }
              end
              return { ok=false, kind="fail",
                       msg="L1* is still non-regular "
                        .. "(Kleene-star does not smooth out "
                        .. "this language)" }
          end },
    },
}

-- ---------- 3.3: DFA minimisation ----------

local Q6 = { "q0","q1","q2","q3","q4","q5" }
local Q7 = { "q0","q1","q2","q3","q4","q5","q6" }

local D1 = "({q0,q1,q2,q3,q4,q5},{a,b},"
    .. "{(q0,a,q1),(q0,b,q3),(q1,a,q1),(q1,b,q2),"
    .. "(q2,a,q2),(q2,b,q5),(q3,a,q3),(q3,b,q4),"
    .. "(q4,a,q4),(q4,b,q5),(q5,a,q5),(q5,b,q5)},"
    .. "q0,{q5})"

local D2 = "({q0,q1,q2,q3,q4,q5},{a,b},"
    .. "{(q0,a,q1),(q0,b,q3),(q1,a,q2),(q1,b,q3),"
    .. "(q2,a,q5),(q2,b,q2),(q3,a,q4),(q3,b,q1),"
    .. "(q4,a,q5),(q4,b,q4),(q5,a,q5),(q5,b,q5)},"
    .. "q0,{q0,q2,q4})"

local D3 = "({q0,q1,q2,q3,q4,q5,q6},{a,b},"
    .. "{(q0,a,q1),(q0,b,q3),(q1,a,q2),(q1,b,q4),"
    .. "(q2,a,q5),(q2,b,q5),(q3,a,q4),(q3,b,q2),"
    .. "(q4,a,q5),(q4,b,q5),(q5,a,q6),(q5,b,q5),"
    .. "(q6,a,q6),(q6,b,q6)},"
    .. "q0,{q1,q3,q5,q6})"

local DC = require "wordproof.dfa_check"

-- the lemma as a multiple-argument choice
local LEMMA_PART = {
    kind="choice", sub="★)",
    label="Lemma: if q_i ~ q_j are equivalent states and "
       .. "δ̂(q_i,u)=q_m, δ̂(q_j,u)=q_n — why are q_m, q_n "
       .. "equivalent?",
    slots = {
        { key="arg", label="argument",
          options = {
            { id="uw", label="If a word w distinguished q_m,q_n "
                .. "then uw would distinguish q_i,q_j — "
                .. "contradiction" },
            { id="det", label="Because the DFA is deterministic "
                .. "the successors are identical" },
            { id="len", label="Because |u| is at most the number "
                .. "of states" },
            { id="same", label="Because q_i and q_j have the same "
                .. "successor on every letter" } } } },
    sel_check = function(sel)
        if sel.arg == "uw" then
            return { ok=true, kind="ok",
                     msg="the distinguishing word lifts through u "
                      .. "— correct" }
        elseif sel.arg == "det" then
            return { ok=false, kind="fail",
                     msg="equivalent states need not have "
                      .. "identical successors — that is what "
                      .. "merging exploits" }
        end
        return { ok=false, kind="fail",
                 msg="that does not prove it — think about what "
                  .. "a distinguishing word for q_m,q_n would "
                  .. "imply for q_i,q_j" }
    end,
}

local function mtask(id, letter, dfa_str, states, extra_part)
    local ncls = #DC.dfa_equiv_classes(dfa_str, states)
    local ps = {}
    if extra_part then ps[#ps+1] = extra_part end
    ps[#ps+1] = { kind="min_table", reference=dfa_str, states=states,
        sub="a)", label="Mark every distinguishable pair "
         .. "(tick the box), give a distinguishing word for each "
         .. "marked pair, and write the equivalence classes as "
         .. "{q0,q3} {q1,q4} …" }
    ps[#ps+1] = { kind="aut", aut_type="dfa", alphabet="a,b",
        reference=dfa_str, exact_states=ncls,
        sub="b)", label="Draw the minimised DFA (it has " .. ncls
         .. " states)" }
    parts_task{
        id = id, letter = letter,
        title = "DFA minimisation",
        desc = "Algorithm 5.7.2: a pair {p,q} is distinguishable "
            .. "when exactly one of p,q is final, or when some "
            .. "letter moves it into a distinguishable pair.",
        given = { kind="table", dfa=dfa_str },
        parts = ps,
    }
end

mtask("3.3a", "A", D1, Q6, LEMMA_PART)
mtask("3.3b", "B", D2, Q6)
mtask("3.3c", "C", D3, Q7)

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
        { id="1.2", title="Exercise 1.2",
          subtasks = {"1.2a","1.2b","1.2c","1.2d","1.2e","1.2f"} },
        { id="1.3", title="Exercise 1.3",
          subtasks = {"1.3j","1.3k","1.3l"} },
      }},
    { id="sheet2", title="Sheet 2",
      groups = {
        { id="2.1", title="Exercise 2.1",
          subtasks = {"2.1m"} },
        { id="2.2", title="Exercise 2.2",
          subtasks = {"2.2n","2.2o","2.2p"} },
        { id="2.3", title="Exercise 2.3",
          subtasks = {"2.3q","2.3u"} },
        { id="2.4", title="Exercise 2.4",
          subtasks = {"2.4r","2.4s"} },
        { id="2.5", title="Exercise 2.5",
          subtasks = {"2.5t"} },
      }},
    { id="sheet3", title="Sheet 3",
      groups = {
        { id="3.1", title="Exercise 3.1",
          subtasks = {"3.1p"} },
        { id="3.2", title="Exercise 3.2",
          subtasks = {"3.2c","3.2e"} },
        { id="3.3", title="Exercise 3.3",
          subtasks = {"3.3a","3.3b","3.3c"} },
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
                    variants = t and t.variants or nil,
                    sub = (t and t.letter)
                          or (sid:match("(%a)$") or sid):upper(),
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
local function view_part(pd, pi)
    local v = { kind=pd.kind, label=pd.label,
                sub=pd.sub or string.char(96 + pi) .. ")",
                optional = pd.optional or false }
    if pd.kind == "aut" then
        v.aut_type, v.alphabet = pd.aut_type, pd.alphabet
        v.with_regexp = pd.with_regexp or false
        v.checks = pd.checks
        v.initial = pd.initial
        v.readonly = pd.readonly or false
        v.seeds = pd.seeds
        -- guided construction: stage id, locked-component list,
        -- simplify-source, checker override
        v.sid = pd.sid
        v.seeds_locked = pd.seeds_locked
        v.takeover_from = pd.takeover_from
        v.check = pd.check
    elseif pd.kind == "choice" then
        v.slots = pd.slots
    elseif pd.kind == "pumping" then
        v.lang = pd.lang
    elseif pd.kind == "min_table" then
        v.states = pd.states
    elseif pd.kind == "trace" or pd.kind == "accept" then
        v.words = pd.words
    elseif pd.kind == "table" or pd.kind == "stable" then
        v.states, v.alphabet = pd.states, pd.alphabet
        v.initial, v.accepting = pd.initial, pd.accepting
    elseif pd.kind == "closure" then
        v.states = pd.states
    end
    return v
end

local function view_given(g)
    if not g then return nil end
    if g.kind == "table" then
        -- render the reference DFA's transition table as plain data;
        -- the GUI builds the HTML table
        local dfa = require("automata").parse_dfa(g.dfa)
        local syms, states, rows = {}, {}, {}
        for s,_ in pairs(dfa:get_symbols()) do syms[#syms+1] = s end
        table.sort(syms)
        for s,_ in pairs(dfa:get_states()) do states[#states+1]=s end
        table.sort(states)
        for _,q in ipairs(states) do
            local r = { state=q,
                        initial = dfa:get_initial() == q,
                        accepting = dfa:is_accepting(q) }
            for _,s in ipairs(syms) do
                r[s] = dfa:get_to_states(q, s)
            end
            rows[#rows+1] = r
        end
        return { kind="table", symbols=syms, rows=rows }
    elseif g.kind == "aut" then
        return { kind="aut", model=g.model, readonly=g.readonly,
                 alphabet=g.alphabet, aut_type=g.aut_type }
    end
end

function M.view(task)
    if task.type == "parts" then
        local parts = {}
        for i,pd in ipairs(task.parts or {}) do
            parts[#parts+1] = view_part(pd, i)
        end
        return {
            id=task.id, type="parts",
            title=task.title, desc=task.desc,
            given=view_given(task.given),
            parts=parts,
        }
    end
    if task.type == "regexp" then
        return {
            id=task.id, type="regexp",
            title=task.title, desc=task.desc,
        }
    end
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
