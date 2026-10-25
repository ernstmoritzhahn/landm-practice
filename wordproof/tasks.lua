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
          label="E = aa(a|b)+bb", reference=R21d_DFA },
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
                sub=string.char(96 + pi) .. ")",
                optional = pd.optional or false }
    if pd.kind == "aut" then
        v.aut_type, v.alphabet = pd.aut_type, pd.alphabet
        v.with_regexp = pd.with_regexp or false
        v.checks = pd.checks
        v.initial = pd.initial
        v.readonly = pd.readonly or false
        v.seeds = pd.seeds
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
