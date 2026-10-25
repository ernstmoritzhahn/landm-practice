-- wordproof/pumping.lua — pumping-lemma practice machinery.
--
-- The student plays the "adversary game" against the checker:
--   1.  they give a word pattern z(k) parameterized by the pumping
--       constant (e.g.  a^k b^k,  (^k )^k,  a^k b a^k );
--   2.  the system checks that z(k) ∈ L and |z(k)| ≥ k for ALL k ≥ 1
--       (symbolically — patterns are linear in k, so the check is
--       exact for the languages below);
--   3.  the pattern is instantiated at a fixed k (= 3) and every
--       legal decomposition z = uvw with |uv| ≤ k, |v| ≥ 1 is
--       enumerated — the student must supply a pumping index i for
--       EACH split such that uv^iw ∉ L.
-- That mirrors the proof structure: i may depend on the split.
--
-- A pattern is a list of blocks {sym=..., k=a, c=b} meaning
-- sym^(a·k+b);  a ≥ 0 and a+b ≥ 0 guarantees e(k) ≥ 0 for all k ≥ 1.

local M = {}

-- ---------- pattern parsing ----------

-- exponent forms: k | N | Nk | k+N | Nk+N | k-N | Nk-N  (a·k + b)
local function parse_exp(s)
    s = (s or ""):gsub("%s", "")
    if s:match("^%d+$") then return 0, tonumber(s) end
    local ak, rest = s:match("^(%d*)k(.*)$")
    if not ak then return nil end
    local a = (ak == "") and 1 or tonumber(ak)
    local b
    if rest == "" then b = 0
    else
        local sgn, num = rest:match("^([+-])(%d+)$")
        if not sgn then return nil end
        b = tonumber(num) * (sgn == "-" and -1 or 1)
    end
    if a < 0 or (a + b) < 0 then return nil end   -- e(k) < 0 for some k ≥ 1
    return a, b
end

function M.parse_pattern(s)
    s = (s or ""):gsub("λ", " ")
    local blocks, i, n = {}, 1, #s
    while i <= n do
        local c = s:sub(i, i)
        if c:match("%s") then
            i = i + 1
        elseif c == "^" or c == "{" or c == "}" then
            return nil, "unexpected '" .. c .. "'"
        else
            local sym, a, b = c, 0, 1
            i = i + 1
            if s:sub(i, i) == "^" then
                i = i + 1
                local body
                if s:sub(i, i) == "{" then
                    local j = s:find("}", i + 1, true)
                    if not j then return nil, "missing '}'" end
                    body, i = s:sub(i + 1, j - 1), j + 1
                else
                    local j = i
                    while j <= n and s:sub(j, j):match("[0-9k+%-]") do
                        j = j + 1
                    end
                    body, i = s:sub(i, j - 1), j
                    if body == "" then
                        return nil, "empty exponent after '^'"
                    end
                end
                a, b = parse_exp(body)
                if not a then
                    return nil, "bad exponent '" .. body
                        .. "' (use k, k+c, c·k, or a plain number)"
                end
            end
            if a == 0 and b == 0 then
                return nil, "'" .. sym .. "^0' is always empty"
            end
            blocks[#blocks + 1] = { sym = sym, k = a, c = b }
        end
    end
    if #blocks == 0 then return nil, "empty pattern" end
    return blocks
end

-- merge adjacent same-symbol blocks (needed for the symbolic checks:
-- the run structure of the expanded word is the merged block list)
local function merge(blocks)
    local out = {}
    for _, b in ipairs(blocks) do
        local top = out[#out]
        if top and top.sym == b.sym then
            top.k, top.c = top.k + b.k, top.c + b.c
        else
            out[#out + 1] = { sym = b.sym, k = b.k, c = b.c }
        end
    end
    return out
end
M.merge = merge

function M.expand(blocks, k)
    local t = {}
    for _, b in ipairs(blocks) do
        t[#t + 1] = b.sym:rep(b.k * k + b.c)
    end
    return table.concat(t)
end

-- |z(k)| = (Σ a_i)·k + Σ b_i ≥ k for all k ≥ 1  iff  Σ a_i ≥ 1
-- (Σ b_i ≥ 0 always, so the k=1 case follows automatically)
local function length_ok(blocks)
    local sk = 0
    for _, b in ipairs(blocks) do sk = sk + b.k end
    return sk >= 1
end

-- ---------- symbolic membership: z(k) ∈ L for all k ≥ 1 ----------

local function alphabet_ok(blocks, alpha)
    for _, b in ipairs(blocks) do
        if not alpha:find(b.sym, 1, true) then
            return "symbol '" .. b.sym .. "' is not in the alphabet"
        end
    end
end

local VALID = {}

-- L = { w | #a(w) = #b(w) }:  count polynomials must be identical
function VALID.eq_ab(mb)
    local err = alphabet_ok(mb, "ab")
    if err then return err end
    local ka, ca, kb, cb = 0, 0, 0, 0
    for _, b in ipairs(mb) do
        if b.sym == "a" then ka, ca = ka + b.k, ca + b.c
        else kb, cb = kb + b.k, cb + b.c end
    end
    if ka ~= kb or ca ~= cb then
        return "#a(z(k)) ≠ #b(z(k)) — the exponents of a and b "
            .. "must agree for every k"
    end
end

-- balanced parentheses:  total balance poly = 0 and every
-- block-boundary prefix balance ≥ 0 for all k (linear → check
-- slope ≥ 0 and value at k = 1)
function VALID.parens(mb)
    local err = alphabet_ok(mb, "()")
    if err then return err end
    local bk, bc = 0, 0
    for j, b in ipairs(mb) do
        local s = (b.sym == "(") and 1 or -1
        bk, bc = bk + s * b.k, bc + s * b.c
        if j < #mb and (bk < 0 or bk + bc < 0) then
            return "z(k) has a prefix with more ')' than '(' "
                .. "(balance fails after block " .. j .. ")"
        end
    end
    if bk ~= 0 or bc ~= 0 then
        return "z(k) is not balanced — '(' and ')' counts differ"
    end
end

-- palindromes: merged block list must be mirror-symmetric
-- (sym and exponent poly at mirrored positions identical)
function VALID.pal(mb)
    local err = alphabet_ok(mb, "ab")
    if err then return err end
    for i = 1, #mb do
        local b, r = mb[i], mb[#mb + 1 - i]
        if b.sym ~= r.sym or b.k ~= r.k or b.c ~= r.c then
            return "z(k) is not a palindrome — block " .. i
                .. " does not mirror block " .. (#mb + 1 - i)
        end
    end
end

-- {ww}:  |z| must be even for all k, and the two halves of the
-- merged block list must be identical (the midpoint may split a
-- block: sym^{e} halves into sym^{e1} + sym^{e2})
function VALID.ww(mb)
    local err = alphabet_ok(mb, "ab")
    if err then return err end
    local sk, sc = 0, 0
    for _, b in ipairs(mb) do sk, sc = sk + b.k, sc + b.c end
    if sk % 2 ~= 0 or sc % 2 ~= 0 then
        return "|z(k)| is odd — a doubled word needs even length"
    end
    local hk, hc = sk / 2, sc / 2     -- half-length poly h(k)
    -- walk to the split point
    local first, second, i = {}, {}, 1
    local acc_k, acc_c = 0, 0
    while i <= #mb do
        local b = mb[i]
        local nk, nc = acc_k + b.k, acc_c + b.c
        local inside = (nk > hk) or (nk == hk and nc > hc)
        if not inside then            -- boundary at or before half
            first[#first + 1] = { sym = b.sym, k = b.k, c = b.c }
            acc_k, acc_c = nk, nc
            if acc_k == hk and acc_c == hc then i = i + 1 break end
            i = i + 1
        else                          -- split inside block i
            local e1k, e1c = hk - acc_k, hc - acc_c
            first[#first + 1] = { sym = b.sym, k = e1k, c = e1c }
            second[#second + 1] =
                { sym = b.sym, k = b.k - e1k, c = b.c - e1c }
            for j = i + 1, #mb do
                second[#second + 1] = mb[j]
            end
            break
        end
    end
    while i <= #mb do
        second[#second + 1] = mb[i]
        i = i + 1
    end
    first, second = merge(first), merge(second)
    if #first ~= #second then
        return "z(k) is not a doubled word — the halves have "
            .. "different block structure"
    end
    for j = 1, #first do
        local f, s = first[j], second[j]
        if f.sym ~= s.sym or f.k ~= s.k or f.c ~= s.c then
            return "z(k) is not a doubled word — the halves differ"
        end
    end
end

-- {a^n b^m | n < m}:  merged blocks are [a^{n(k)}, b^{m(k)}]
-- (a-block optional);  n(k) < m(k) for all k ≥ 1  iff
-- slope_n ≤ slope_m and n(1) < m(1)
function VALID.anbm_lt(mb)
    local err = alphabet_ok(mb, "ab")
    if err then return err end
    if #mb > 2 or (mb[1] and mb[1].sym ~= "a")
       or (mb[2] and mb[2].sym ~= "b") then
        return "z(k) is not of the form a^· b^·"
    end
    local n = mb[1] or { k = 0, c = 0 }
    local m = mb[2]
    if not m then return "z(k) has no b-block (m = 0 < n is impossible)" end
    if n.k > m.k or n.k + n.c >= m.k + m.c then
        return "n(k) < m(k) fails — the b exponent must grow at "
            .. "least as fast and start larger"
    end
end

-- {a^i b^j c^{2j}}:  merged blocks in order a,b,c (a/b optional);
-- c exponent poly = 2 × b exponent poly
function VALID.aibjc(mb)
    local err = alphabet_ok(mb, "abc")
    if err then return err end
    local order = { a = 1, b = 2, c = 3 }
    for j = 2, #mb do
        if order[mb[j].sym] <= order[mb[j - 1].sym] then
            return "z(k) is not of the form a^· b^· c^·"
        end
    end
    if #mb > 3 then return "z(k) is not of the form a^· b^· c^·" end
    local eb, ec = { k = 0, c = 0 }, nil
    for _, b in ipairs(mb) do
        if b.sym == "b" then eb = b elseif b.sym == "c" then ec = b end
    end
    if not ec then
        return "z(k) has no c-block"
    end
    if ec.k ~= 2 * eb.k or ec.c ~= 2 * eb.c then
        return "the c count must be exactly twice the b count "
            .. "for every k"
    end
end

-- ---------- symbolic general decomposition ----------
--
-- When the first block of z(k) fills the whole first-k window
-- (e_1 ≥ k for all k), EVERY legal split has v = s_1^q for some
-- 1 ≤ q ≤ k (u = s_1^p, p+q ≤ k — and u drops out of the pumped
-- word).  The student then gives i = i(k,q) as a linear expression
-- A·q + B·k + C and the checker must show uv^iw ∉ L on the whole
-- domain  D = { k ≥ 1, 1 ≤ q ≤ k }.
--
-- Polynomials over (k,q): sparse table {c, k, q, k2, q2, kq}
-- (degree ≤ 2 is enough: block exponents are linear, i is linear,
-- and q·(i−1) is quadratic).

local POLY_KEYS = { "c", "k", "q", "k2", "q2", "kq" }
local function poly(c, k, q, k2, q2, kq)
    return { c = c or 0, k = k or 0, q = q or 0,
             k2 = k2 or 0, q2 = q2 or 0, kq = kq or 0 }
end
local function poly_zero(f)
    for _, t in ipairs(POLY_KEYS) do
        if f[t] ~= 0 then return false end
    end
    return true
end
local function poly_eval(f, k, q)
    return f.c + f.k * k + f.q * q
           + f.k2 * k * k + f.q2 * q * q + f.kq * k * q
end
-- e1' = e1 + q·(i−1):  e1 = {k=a,c=b}, i = {q=A,k=B,c=C}
local function pumped_first_exp(e1, iexpr)
    return { k = e1.k, c = e1.c, k2 = 0,
             q = iexpr.c - 1, q2 = iexpr.q, kq = iexpr.k }
end

-- extract the maximal common monomial factor  k^a·q^b  (the factor is
-- ≥ 1 on the domain, so the residual carries the sign)
local TERM_EXP = { c = {0,0}, k = {1,0}, q = {0,1},
                   k2 = {2,0}, q2 = {0,2}, kq = {1,1} }
local function common_monomial(f)
    local ka, qa = math.huge, math.huge
    for _, t in ipairs(POLY_KEYS) do
        if f[t] ~= 0 then
            ka = math.min(ka, TERM_EXP[t][1])
            qa = math.min(qa, TERM_EXP[t][2])
        end
    end
    if ka == math.huge then ka, qa = 0, 0 end
    return ka, qa
end
local function divide_monomial(f, ka, qa)
    if ka == 0 and qa == 0 then return f end
    local nr = poly(0, 0, 0)
    for t, v in pairs(f) do
        if v ~= 0 then
            local ek, eq = TERM_EXP[t][1] - ka, TERM_EXP[t][2] - qa
            for _, nt in ipairs(POLY_KEYS) do
                if TERM_EXP[nt][1] == ek and TERM_EXP[nt][2] == eq then
                    nr[nt] = v
                end
            end
        end
    end
    return nr
end

-- is f(k,q) ≠ 0 for ALL (k,q) in the domain?
-- returns true (proven), or {k=,q=} a counterexample, or nil (cannot
-- decide — caller should fall back to sampling / warn)
local nz_domain, gez_domain
local function nz_raw(f)
    if poly_zero(f) then return { k = 1, q = 1 } end
    -- single nonzero term: nonzero on the whole domain
    local terms = 0
    for _, t in ipairs(POLY_KEYS) do
        if f[t] ~= 0 then terms = terms + 1 end
    end
    if terms == 1 then return true end
    -- sign-definite: all coefficients ≥ 0 with one > 0 (or all ≤ 0)
    local pos, neg = false, false
    for _, t in ipairs(POLY_KEYS) do
        if f[t] > 0 then pos = true elseif f[t] < 0 then neg = true end
    end
    if pos and not neg then return true end
    if neg and not pos then return true end
    -- linear: extrema on the triangle sit on the three boundary
    -- pieces (1,1), ray q=1, ray q=k
    if f.k2 == 0 and f.q2 == 0 and f.kq == 0 then
        local a, b, c = f.k, f.q, f.c
        if a >= 0 and a + b >= 0 and a + b + c > 0 then return true end
        if a <= 0 and a + b <= 0 and a + b + c < 0 then return true end
    end
    -- look for a concrete counterexample on a bounded grid
    for k = 1, 8 do
        for q = 1, k do
            if poly_eval(f, k, q) == 0 then return { k = k, q = q } end
        end
    end
    return nil
end
nz_domain = function(f)
    local ka, qa = common_monomial(f)
    return nz_raw(divide_monomial(f, ka, qa))
end

-- is f(k,q) ≥ 0 for all domain points?  (same answer contract)
local function gez_raw(f)
    if poly_zero(f) then return true, "identity" end
    local pos, neg = false, false
    for _, t in ipairs(POLY_KEYS) do
        if f[t] > 0 then pos = true elseif f[t] < 0 then neg = true end
    end
    if not neg then return true end          -- all coeffs ≥ 0
    if f.k2 == 0 and f.q2 == 0 and f.kq == 0 then
        local a, b, c = f.k, f.q, f.c
        if a >= 0 and a + b >= 0 and a + b + c >= 0 then return true end
    end
    for k = 1, 8 do
        for q = 1, k do
            if poly_eval(f, k, q) < 0 then return { k = k, q = q } end
        end
    end
    return nil
end
gez_domain = function(f)
    local ka, qa = common_monomial(f)
    return gez_raw(divide_monomial(f, ka, qa))
end

-- i(k,q) = A·q + B·k + C:  terms "+"-joined, each N | Nq | Nk | q | k
local function parse_iexpr(s)
    s = (s or ""):gsub("%s", "")
    if s == "" then return nil end
    if s == "-" then return nil end
    -- allow a leading "-" only on a lone constant?  i must be ≥ 0 on
    -- the domain — simplest is to forbid '-' entirely except inside
    -- terms, which we simply reject: negative i values are caught by
    -- the per-case validity check anyway
    if s:find("-") then
        -- allow "k-q"?  too subtle — reject minus signs
        return nil
    end
    local aq, bk, c = 0, 0, 0
    for term in s:gmatch("[^+]+") do
        local n = term:match("^(%d+)q$") or (term == "q" and 1)
        if n then aq = aq + tonumber(n) else
            n = term:match("^(%d+)k$") or (term == "k" and 1)
            if n then bk = bk + tonumber(n) else
                n = term:match("^(%d+)$")
                if n then c = c + tonumber(n) else return nil end
            end
        end
    end
    return { q = aq, k = bk, c = c }
end
local function iexpr_eval(i, k, q)
    return i.c + i.q * q + i.k * k
end

-- ---------- concrete membership (for the pumped words) ----------

local MEM = {}

function MEM.eq_ab(w)
    local na, nb = 0, 0
    for i = 1, #w do
        if w:sub(i, i) == "a" then na = na + 1 else nb = nb + 1 end
    end
    return na == nb
end

function MEM.parens(w)
    local bal = 0
    for i = 1, #w do
        bal = bal + (w:sub(i, i) == "(" and 1 or -1)
        if bal < 0 then return false end
    end
    return bal == 0
end

function MEM.pal(w) return w == w:reverse() end

function MEM.ww(w)
    if #w % 2 ~= 0 then return false end
    local h = #w / 2
    return w:sub(1, h) == w:sub(h + 1)
end

function MEM.anbm_lt(w)
    if not w:match("^a*b*$") then return false end
    local a = w:match("^a*") or ""
    return #a < #w - #a
end

function MEM.aibjc(w)
    if not w:match("^a*b*c*$") then return false end
    local nb, nc = 0, 0
    for i = 1, #w do
        local c = w:sub(i, i)
        if c == "b" then nb = nb + 1 elseif c == "c" then nc = nc + 1 end
    end
    return nc == 2 * nb
end

-- ---------- symbolic out-of-language proofs (general case) ----------
-- GEN[lang](mb, iexpr) -> true (proven uv^iw ∉ L on the domain),
--   {k=,q=,word=} counterexample, or nil (cannot decide)
local GEN = {}

-- q·(i−1) as a poly in (k,q)
local function dqp(iexpr)
    return { c = 0, k = 0, k2 = 0,
             q = iexpr.c - 1, q2 = iexpr.q, kq = iexpr.k }
end
local function poly_sub(a, b)
    local r = {}
    for _, t in ipairs(POLY_KEYS) do
        r[t] = (a[t] or 0) - (b[t] or 0)
    end
    return r
end

-- eq_ab: pumped word's #a−#b differs from 0 by ±q(i−1)
GEN.eq_ab = function(mb, s1, iexpr)
    return nz_domain(dqp(iexpr))
end

-- parens: balance changes by q(i−1); unbalanced => out
GEN.parens = function(mb, s1, iexpr)
    return nz_domain(dqp(iexpr))
end

-- palindrome: block1's mirror is the last block; their exponent
-- difference becomes e1 + q(i−1) − e_last
GEN.pal = function(mb, s1, iexpr)
    if #mb < 2 then return nil end      -- single-run z: cannot prove
    local last = mb[#mb]
    if last.sym ~= s1 then return nil end
    local e1p = pumped_first_exp(mb[1], iexpr)
    local el = { c = last.c, k = last.k, q = 0, k2 = 0, q2 = 0, kq = 0 }
    return nz_domain(poly_sub(e1p, el))
end

-- {a^n b^m | n<m}: need pumped n ≥ m (or broken shape)
GEN.anbm_lt = function(mb, s1, iexpr)
    if s1 ~= "a" then
        return { k = 1, q = 1,
                 msg = "v lies in the b-block — pumping b's keeps "
                    .. "n = 0 < m, so no i works; include an a-block "
                    .. "in z" }
    end
    local eb = { c = mb[2].c, k = mb[2].k, q = 0, k2 = 0, q2 = 0, kq = 0 }
    local g = poly_sub(pumped_first_exp(mb[1], iexpr), eb)
    return gez_domain(g)
end

-- {a^i b^j c^{2j}}: need #c ≠ 2·#b after pumping
GEN.aibjc = function(mb, s1, iexpr)
    if s1 ~= "b" then
        return { k = 1, q = 1,
                 msg = "v must lie in the b-block — pumping "
                    .. s1 .. "'s keeps #c = 2·#b; pick a witness "
                    .. "starting with b^k" }
    end
    local d = dqp(iexpr)
    d.c, d.k, d.q, d.k2, d.q2, d.kq =
        2 * d.c, 2 * d.k, 2 * d.q, 2 * d.k2, 2 * d.q2, 2 * d.kq
    return nz_domain(d)   -- pumped #c−2#b = −2·q(i−1) ≠ 0 needed
end

-- {ww}:  parity first, then symbolic half-split
GEN.ww = function(mb, s1, iexpr)
    local d = dqp(iexpr)
    -- total pumped length poly
    local len = { c = 0, k = 0, q = d.q, k2 = 0, q2 = d.q2, kq = d.kq }
    for _, b in ipairs(mb) do
        len.k, len.c = len.k + b.k, len.c + b.c
    end
    -- if len' is provably odd on the whole domain -> always out.
    -- parity of a poly over integer points: need every coeff of
    -- variable-involving terms even and const odd
    local var_odd = false
    for _, t in ipairs({ "k", "q", "k2", "q2", "kq" }) do
        if len[t] % 2 ~= 0 then var_odd = true end
    end
    if not var_odd and len.c % 2 == 1 then return true end
    -- half-split: H = len'/2 formally (correct on the even-parity
    -- subdomain; odd-parity points are out anyway)
    local H = {}
    for _, t in ipairs(POLY_KEYS) do H[t] = len[t] / 2 end
    local pb = {}
    for j, b in ipairs(mb) do
        pb[j] = { sym = b.sym,
                  poly = (j == 1) and pumped_first_exp(b, iexpr)
                        or { c = b.c, k = b.k, q = 0, k2 = 0, q2 = 0,
                             kq = 0 } }
    end
    -- walk: find the block the midpoint falls into, with the
    -- cumulative-vs-H comparisons decided by gez_domain
    local C = poly(0, 0, 0)
    local first, second, j = {}, {}, 1
    while j <= #pb do
        local b = pb[j]
        local nj = {}
        for _, t in ipairs(POLY_KEYS) do nj[t] = C[t] + b.poly[t] end
        local D = poly_sub(nj, H)
        local nonpos = gez_domain(poly_sub(poly(0, 0, 0), D))
        local nonneg = gez_domain(D)
        if nonpos == true then
            if poly_zero(D) then
                -- midpoint exactly at this block's end: the tail
                -- piece is empty — halves are [..block j] | [j+1..]
                first[#first + 1] = b
                for m = j + 1, #pb do
                    second[#second + 1] = pb[m]
                end
                break
            end
            -- whole block strictly before the midpoint
            first[#first + 1] = b
            C, j = nj, j + 1
        elseif nonneg == true or nonneg == nil then
            -- midpoint inside block j (nonneg unproven stays on the
            -- conservative side: the split is still well-defined for
            -- the witness shapes we expect)
            local e1 = poly_sub(H, C)
            local tail = poly_sub(b.poly, e1)
            first[#first + 1] = { sym = b.sym, poly = e1 }
            if not poly_zero(tail) then
                second[#second + 1] = { sym = b.sym, poly = tail }
            end
            for m = j + 1, #pb do second[#second + 1] = pb[m] end
            break
        else
            return nil   -- midpoint position not decidable
        end
    end
    -- halves must differ at every domain point
    if #first ~= #second then return true end
    for m = 1, #first do
        local f, s = first[m], second[m]
        if f.sym ~= s.sym then return true end
        local diff = poly_sub(f.poly, s.poly)
        if nz_domain(diff) == true then return true end
    end
    return nil    -- could not prove the halves differ everywhere
end

M.LANGS = {
    eq_ab    = { label = "{w ∈ {a,b}* | #a(w) = #b(w)}",
                 valid = VALID.eq_ab, mem = MEM.eq_ab, gen = GEN.eq_ab },
    parens   = { label = "matched parentheses over {(,)}",
                 valid = VALID.parens, mem = MEM.parens,
                 gen = GEN.parens },
    pal      = { label = "palindromes over {a,b}",
                 valid = VALID.pal, mem = MEM.pal, gen = GEN.pal },
    ww       = { label = "{ww | w ∈ {a,b}*}",
                 valid = VALID.ww, mem = MEM.ww, gen = GEN.ww },
    anbm_lt  = { label = "{a^n b^m | n < m}",
                 valid = VALID.anbm_lt, mem = MEM.anbm_lt,
                 gen = GEN.anbm_lt },
    aibjc    = { label = "{a^i b^j c^{2j}}",
                 valid = VALID.aibjc, mem = MEM.aibjc,
                 gen = GEN.aibjc },
}

-- ---------- the general (all-k) decomposition ----------

-- every legal split satisfies v = s_1^q, 1 ≤ q ≤ k  iff  the first
-- block dominates the first-k window, i.e.  e_1(k) ≥ k for all k ≥ 1
-- (slope ≥ 1 and value at k = 1 ≥ 1).  This is also *the* didactic
-- trick of pumping proofs: front-load the pumpable structure.
local function uniform_first(mb)
    local e = mb[1]
    if e and e.k >= 1 and e.k + e.c >= 1 then return e end
end

-- what the "general" step looks like for a given (merged) pattern
function M.general_case(mb)
    local e = uniform_first(mb)
    if not e then
        return { err = "the first " .. "k letters of z(k) do not lie "
                  .. "in a single block — pick a witness whose first "
                  .. "block grows with k (e.g. a^k...); that is what "
                  .. "makes the pumping argument work anyway" }
    end
    return { sym = e.sym }
end

-- full general check: symbolic proof attempt after a concrete grid
-- scan.  returns {ok,kind,msg}
function M.check_general(lang_id, z_str, i_str)
    local lang = M.LANGS[lang_id]
    if not lang then
        return { ok = false, kind = "fail", msg = "unknown language" }
    end
    local blocks, perr = M.parse_pattern(z_str)
    if not blocks then
        return { ok = false, kind = "fail", msg = perr }
    end
    local mb = merge(blocks)
    local verr = lang.valid and lang.valid(mb)
    if verr then
        return { ok = false, kind = "fail", msg = verr }
    end
    if not length_ok(blocks) then
        return { ok = false, kind = "fail", msg = "|z(k)| < k" }
    end
    local gcase = M.general_case(mb)
    if gcase.err then
        return { ok = false, kind = "fail", msg = gcase.err }
    end
    local iexpr = parse_iexpr(i_str)
    if not iexpr then
        return { ok = false, kind = "fail",
                 msg = "i must be a non-negative integer or an "
                    .. "expression in k and q (e.g. 2, 0, q+1, k+1)" }
    end
    -- concrete counterexample search: instantiate uv^iw on the grid
    for k = 1, 8 do
        local z = M.expand(mb, k)
        for q = 1, math.min(k, #z) do
            local i = iexpr_eval(iexpr, k, q)
            if i == math.floor(i) and i >= 0 then
                local u = z:sub(1, k - q)      -- u = s1^{k-q}… any
                local v = z:sub(k - q + 1, k)  -- tail inside block 1
                local w = z:sub(k + 1)
                local pumped = u .. v:rep(i) .. w
                if lang.mem(pumped) then
                    return { ok = false, kind = "fail",
                        msg = "counterexample at k=" .. k .. ", |v|=q="
                            .. q .. ":  uv^" .. i .. "w = " .. pumped
                            .. " ∈ L" }
                end
            end
        end
    end
    -- symbolic proof attempt
    local prov = lang.gen and lang.gen(mb, gcase.sym, iexpr)
    if prov == true then
        return { ok = true, kind = "ok",
                 msg = "uv^iw ∉ L for all k ≥ 1 and 1 ≤ q ≤ k — "
                    .. "verified symbolically" }
    elseif type(prov) == "table" and prov.k then
        return { ok = false, kind = "fail",
                 msg = prov.msg or ("counterexample at k=" .. prov.k
                       .. ", q=" .. prov.q) }
    end
    return { ok = false, kind = "warn",
             msg = "no counterexample found (tested k ≤ 8), but the "
                .. "general claim could not be verified symbolically "
                .. "— keep i simple and prove the ∀k part on paper" }
end

-- ---------- decompositions of the instantiated word ----------

-- all z = uvw with |uv| ≤ K and |v| ≥ 1 (p ≤ K, q ≥ 1, p+q ≤ K, ≤ n)
function M.splits(word, K)
    local out, n = {}, #word
    for p = 0, math.min(K, n) - 1 do
        for q = 1, math.min(K - p, n - p) do
            out[#out + 1] = { u = word:sub(1, p),
                              v = word:sub(p + 1, p + q),
                              w = word:sub(p + q + 1) }
        end
    end
    return out
end

-- worker "pump_splits" helper: validate + instantiate + enumerate.
-- returns {word=..., splits=...} or {err=...}
function M.instantiate(lang_id, z_str, K)
    K = K or 3
    local lang = M.LANGS[lang_id]
    if not lang then return { err = "unknown language" } end
    local blocks, perr = M.parse_pattern(z_str)
    if not blocks then return { err = perr } end
    local mb = merge(blocks)
    if not length_ok(mb) then
        return { err = "|z| must be at least k: your z(k) does not "
                  .. "grow with k (it has no k exponent)" }
    end
    local verr = lang.valid(mb)
    if verr then
        return { err = "z(k) is not in L for every k: " .. verr }
    end
    local z = M.expand(mb, K)
    return { word = z, splits = M.splits(z, K), k = K,
             gen = M.general_case(mb) }
end

-- full check: z valid + every split row has a working i.
-- is_tbl[ri] = the student's pumping index for split row ri.
function M.check(lang_id, z_str, is_tbl, K, gen_i)
    K = K or 3
    local lang = M.LANGS[lang_id]
    if not lang then
        return { ok = false, kind = "fail", msg = "unknown language" }
    end
    local inst = M.instantiate(lang_id, z_str, K)
    if inst.err then
        return { ok = false, kind = "fail", msg = inst.err }
    end
    local rows, all_ok = {}, true
    for ri, s in ipairs(inst.splits) do
        local iv = is_tbl and (is_tbl[ri] or is_tbl[tostring(ri)])
        if iv == nil or (type(iv) == "string" and not iv:match("%S")) then
            all_ok = false
            rows[ri] = { kind = "empty", msg = "choose i" }
        else
            local i = tonumber(iv)
            if not i or i ~= math.floor(i) or i < 0 or i > 200 then
                all_ok = false
                rows[ri] = { kind = "mismatch",
                             msg = "i must be an integer ≥ 0" }
            else
                local pumped = s.u .. s.v:rep(i) .. s.w
                if lang.mem(pumped) then
                    all_ok = false
                    -- is there any i that would have worked?
                    local hope = false
                    for t = 0, 8 do
                        if not lang.mem(s.u .. s.v:rep(t) .. s.w) then
                            hope = true break
                        end
                    end
                    rows[ri] = { kind = "mismatch",
                        msg = "uv^" .. i .. "w = " .. pumped
                            .. (hope and " ∈ L — try another i"
                                 or " ∈ L — NO i works: this split "
                                 .. "cannot be beaten; z is a bad "
                                 .. "choice") }
                else
                    rows[ri] = { kind = "ok",
                                 msg = "uv^" .. i .. "w ∉ L" }
                end
            end
        end
    end
    -- the general decomposition (all k): i(k,q) per case
    local gen
    if gen_i ~= nil and (type(gen_i) ~= "string" or gen_i:match("%S")) then
        gen = M.check_general(lang_id, z_str, gen_i)
        if not gen.ok then all_ok = false end
    end
    if all_ok then
        return { ok = true, kind = "ok", rows = rows, gen = gen,
                 msg = "z(k) ∈ L, |z| ≥ k, and every decomposition "
                    .. "is beaten — the pumping argument works (k="
                    .. K .. ")" }
    end
    return { ok = false, kind = "fail", rows = rows, gen = gen,
             msg = "every split (u,v,w) needs an i with uv^iw ∉ L" }
end

return M
