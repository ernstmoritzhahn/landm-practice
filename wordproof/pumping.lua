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

-- exponent forms: linear in the variables k,p,q plus a constant:
--  k | N | Nk | k+N | k-p-q | 2q | p+1 | ...   ->  {k,p,q,c} coeffs
--  parenthesised subexpressions work too:  k-(p+q), 2(k-p),
--  2q+(k-p-q);  an optional leading sign is allowed.
local function parse_exp(s)
    s = (s or ""):gsub("%s", "")
    if s == "" then return nil end
    local pos = 1
    local expr                            -- fwd decl (atom recurses)
    local function atom()
        local numstr = s:match("^%d*", pos)
        pos = pos + #numstr
        local num = tonumber(numstr)      -- nil when ""
        local ch = s:sub(pos, pos)
        if ch == "(" then
            pos = pos + 1
            local r = expr()
            if not r or s:sub(pos, pos) ~= ")" then return nil end
            pos = pos + 1
            local n = num or 1            -- N·(expr)
            return { k = n * r.k, p = n * r.p,
                     q = n * r.q, c = n * r.c }
        end
        if ch:match("[kpq]") then
            pos = pos + 1
            local t = { k = 0, p = 0, q = 0, c = 0 }
            t[ch] = num or 1
            return t
        end
        if num then return { k = 0, p = 0, q = 0, c = num } end
        return nil
    end
    expr = function()
        local r = { k = 0, p = 0, q = 0, c = 0 }
        local sgn = 1
        local ch = s:sub(pos, pos)
        if ch == "+" then pos = pos + 1
        elseif ch == "-" then sgn, pos = -1, pos + 1 end
        while pos <= #s do
            local t = atom()
            if not t then return nil end
            r.k = r.k + sgn * t.k
            r.p = r.p + sgn * t.p
            r.q = r.q + sgn * t.q
            r.c = r.c + sgn * t.c
            sgn = 1
            local c2 = s:sub(pos, pos)
            if c2 == "+" or c2 == "-" then
                if c2 == "-" then sgn = -1 end
                pos = pos + 1
            else
                break
            end
        end
        return r
    end
    local r = expr()
    if not r or pos <= #s then return nil end
    return r
end

local function exp_ge0_k(r)   -- e(k) ≥ 0 for all k ≥ 1 when p,q = 0
    return r.k >= 0 and r.k + r.c >= 0 and r.p == 0 and r.q == 0
end

-- shared block scanner: sym [^ exponent] where the exponent is
--  ^{expr}, ^(expr) or ^expr (chars from [0-9kpq+-]).
--  Unicode dashes are normalised to '-' so keyboard-composed
--  input does not break parsing.
local function scan_blocks(s, check, allow_zero)
    s = (s or ""):gsub("λ", " ")
       :gsub("\\lambda", " "):gsub("\\lamda", " ")
       :gsub("lambda", " "):gsub("lamda", " ")
        :gsub("\xe2\x88\x92", "-")   -- −  minus sign
        :gsub("\xe2\x80\x93", "-")   -- –  en dash
        :gsub("\xe2\x80\x94", "-")   -- —  em dash
    local blocks, i, n = {}, 1, #s
    while i <= n do
        local c = s:sub(i, i)
        if c:match("%s") then
            i = i + 1
        elseif c == "^" or c == "{" or c == "}" then
            return nil, "unexpected '" .. c .. "'"
        else
            local sym, e = c, { k = 0, p = 0, q = 0, c = 1 }
            i = i + 1
            if s:sub(i, i) == "^" then
                i = i + 1
                local body
                local open = s:sub(i, i)
                if open == "{" or open == "(" then
                    local close = open == "{" and "}" or ")"
                    -- scan to the matching close; nested parens
                    -- inside the body are balanced out
                    local j, depth = i + 1, 0
                    while j <= n do
                        local cj = s:sub(j, j)
                        if cj == close and depth == 0 then break end
                        if cj == "(" then depth = depth + 1
                        elseif cj == ")" then depth = depth - 1 end
                        j = j + 1
                    end
                    if j > n then
                        return nil, "missing '" .. close .. "'"
                    end
                    body, i = s:sub(i + 1, j - 1), j + 1
                else
                    -- bare exponent: NO parentheses in the
                    -- charset — a bare '(' or ')' may be a symbol
                    -- of the pattern itself (the parens language)
                    -- and must start a new block
                    local j = i
                    while j <= n
                        and s:sub(j, j):match("[0-9kpq+%-]") do
                        j = j + 1
                    end
                    body, i = s:sub(i, j - 1), j
                end
                if body == "" then
                    return nil, "empty exponent — drop the block "
                        .. "or give it a length (e.g. b^{k-p-q})"
                end
                e = parse_exp(body)
                if not e then
                    return nil, "bad exponent '" .. body
                        .. "' (linear in k, p, q plus a constant; "
                        .. "parentheses allowed)"
                end
                if check then
                    local cerr = check(sym, e, body)
                    if cerr then return nil, cerr end
                end
            end
            if not allow_zero
               and e.k == 0 and e.p == 0 and e.q == 0
               and e.c == 0 then
                return nil, "'" .. sym .. "^0' is always empty"
            end
            blocks[#blocks + 1] = { sym = sym, k = e.k,
                                    p = e.p, q = e.q, c = e.c }
        end
    end
    if #blocks == 0 then return nil, "empty pattern" end
    return blocks
end

function M.parse_pattern(s)
    return scan_blocks(s, function(sym, e, body)
        if e.p ~= 0 or e.q ~= 0 then
            return "parameters p, q may only appear in the "
                .. "decomposition u, v, w — not in z(k)"
        end
        if not exp_ge0_k(e) then
            return "'" .. sym .. "^" .. body
                .. "' is empty for some k ≥ 1"
        end
    end)
end

-- same grammar, but p and q allowed (for the student-written
-- decomposition u(k,p,q) · v(k,q) · w(k,p,q) and the pumped word).
-- Zero-exponent blocks are allowed here: the honest unexpanded
-- form u·v^i·w may legitimately contain e.g. a^{0q} when i = 0 —
-- they contribute nothing and are filtered out at comparison.
function M.parse_pattern_pq(s)
    return scan_blocks(s, nil, true)
end

-- drop zero-exponent blocks (a^{0q}, a^0): they contribute no
-- letters — legal in the student's unexpanded forms, invisible
-- in the merged run structure
local function nonzero(b)
    return b.k ~= 0 or b.p ~= 0 or b.q ~= 0 or b.c ~= 0
end
local function dropzero(blocks)
    local out = {}
    for _, b in ipairs(blocks) do
        if nonzero(b) then out[#out + 1] = b end
    end
    return out
end

-- merge adjacent same-symbol blocks (needed for the symbolic checks:
-- the run structure of the expanded word is the merged block list)
local function merge(blocks)
    local out = {}
    for _, b in ipairs(blocks) do
        local top = out[#out]
        if top and top.sym == b.sym then
            top.k = top.k + b.k
            top.p = (top.p or 0) + (b.p or 0)
            top.q = (top.q or 0) + (b.q or 0)
            top.c = top.c + b.c
        else
            out[#out + 1] = { sym = b.sym, k = b.k, p = b.p or 0,
                              q = b.q or 0, c = b.c }
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

function M.expand_params(blocks, k, p, q)
    local t = {}
    for _, b in ipairs(blocks) do
        local n = b.k * k + (b.p or 0) * p + (b.q or 0) * q + b.c
        if n > 0 then t[#t + 1] = b.sym:rep(n) end
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
-- For a witness whose first block dominates the first-k window
-- (e_1 ≥ k for all k), every legal split has the form
--   u = s_1^p,  v = s_1^q,  w = s_1^{e_1-p-q} · rest,  p≥0, q≥1,
--   p+q ≤ k
-- The STUDENT writes u, v, w as patterns over the parameters
-- (k,p,q);  the checker verifies  u·v·w ≡ z(k)  as a polynomial
-- identity, legality (|v| ≥ 1, |uv| ≤ k), coverage of every legal
-- split, and then uv^iw ∉ L on
--   D = { k ≥ 1, p ≥ 0, q ≥ 1, p+q ≤ k }
-- for the student's i(k,q) (a linear expression).
--
-- Polynomials over (k,p,q): sparse table over keys
-- {c, k, p, q, k2, p2, q2, kp, kq, pq} — degree ≤ 2 is enough:
-- exponents are linear, i is linear, v^i contributes quadratic.

local POLY_KEYS = { "c", "k", "p", "q",
                    "k2", "p2", "q2", "kp", "kq", "pq" }
local TERM_EXP = { c={0,0,0}, k={1,0,0}, p={0,1,0}, q={0,0,1},
                   k2={2,0,0}, p2={0,2,0}, q2={0,0,2},
                   kp={1,1,0}, kq={1,0,1}, pq={0,1,1} }
local function poly(t)
    local r = {}
    for _, k2 in ipairs(POLY_KEYS) do r[k2] = t[k2] or 0 end
    return r
end
local function poly_zero(f)
    for _, t in ipairs(POLY_KEYS) do
        if (f[t] or 0) ~= 0 then return false end
    end
    return true
end
local function poly_eval(f, k, p, q)
    return f.c + f.k * k + (f.p or 0) * p + f.q * q
           + f.k2 * k * k + (f.p2 or 0) * p * p + f.q2 * q * q
           + (f.kp or 0) * k * p + f.kq * k * q + (f.pq or 0) * p * q
end
local function poly_sub(a, b)
    local r = {}
    for _, t in ipairs(POLY_KEYS) do r[t] = (a[t] or 0) - (b[t] or 0) end
    return r
end
local function poly_scale(a, s)
    local r = {}
    for _, t in ipairs(POLY_KEYS) do r[t] = (a[t] or 0) * s end
    return r
end
-- product of two LINEAR polys (degree ≤ 2 result)
local function poly_mul(a, b)
    local r = poly({})
    for _, ta in ipairs(POLY_KEYS) do
        local ea = TERM_EXP[ta]
        if (a[ta] or 0) ~= 0 and ea[1] + ea[2] + ea[3] <= 1 then
            for _, tb in ipairs(POLY_KEYS) do
                local eb = TERM_EXP[tb]
                if (b[tb] or 0) ~= 0 and eb[1] + eb[2] + eb[3] <= 1 then
                    local e = { ea[1] + eb[1], ea[2] + eb[2],
                                ea[3] + eb[3] }
                    for _, nt in ipairs(POLY_KEYS) do
                        local ne = TERM_EXP[nt]
                        if ne[1] == e[1] and ne[2] == e[2]
                           and ne[3] == e[3] then
                            r[nt] = r[nt] + a[ta] * b[tb]
                        end
                    end
                end
            end
        end
    end
    return r
end
local function block_poly(b)   -- {sym,k,p,q,c} -> exponent poly
    return poly{ k = b.k or 0, p = b.p or 0, q = b.q or 0,
                 c = b.c or 0 }
end

-- extract the maximal common monomial factor  k^a·p^b·q^c
local function common_monomial(f)
    local mn = { math.huge, math.huge, math.huge }
    for _, t in ipairs(POLY_KEYS) do
        if (f[t] or 0) ~= 0 then
            local e = TERM_EXP[t]
            for d = 1, 3 do mn[d] = math.min(mn[d], e[d]) end
        end
    end
    if mn[1] == math.huge then mn = { 0, 0, 0 } end
    return mn
end
local function divide_monomial(f, mn)
    if mn[1] == 0 and mn[2] == 0 and mn[3] == 0 then return f end
    local nr = poly({})
    for t, v in pairs(f) do
        if v ~= 0 then
            local e = TERM_EXP[t]
            local tgt = { e[1] - mn[1], e[2] - mn[2], e[3] - mn[3] }
            for _, nt in ipairs(POLY_KEYS) do
                local ne = TERM_EXP[nt]
                if ne[1] == tgt[1] and ne[2] == tgt[2]
                   and ne[3] == tgt[3] then nr[nt] = v end
            end
        end
    end
    return nr
end

-- iterate domain grid points (bounded); legal(k,p,q) may restrict
-- the iteration to the student's legal splits
local function each_domain_point(legal, fn)
    for k = 1, 8 do
        for p = 0, k do
            for q = 1, k - p do
                if not legal or legal(k, p, q) then
                    local r = fn(k, p, q)
                    if r ~= nil then return r end
                end
            end
        end
    end
end

-- is f(k,p,q) ≠ 0 for ALL legal domain points?
-- -> true (proven) | {k,p,q} counterexample | nil (undecided)
local nz_domain, gez_domain
local function nz_raw(f, legal)
    if poly_zero(f) then return { k = 1, p = 0, q = 1 } end
    local terms = 0
    for _, t in ipairs(POLY_KEYS) do
        if (f[t] or 0) ~= 0 then terms = terms + 1 end
    end
    if terms == 1 then
        -- a monomial has a zero iff it carries p (p = 0 is in domain)
        -- or only c... check the actual monomial's exponent
        local tn
        for _, t in ipairs(POLY_KEYS) do
            if (f[t] or 0) ~= 0 then tn = t end
        end
        if TERM_EXP[tn][2] > 0 or tn == "c" then
            -- p^b·… with b ≥ 1: p = 0 makes it 0;  bare c ≠ 0 never
            if tn == "c" then return true end
            return { k = 1, p = 0, q = 1 }
        end
        return true
    end
    local pos, neg = false, false
    for _, t in ipairs(POLY_KEYS) do
        if (f[t] or 0) > 0 then pos = true
        elseif (f[t] or 0) < 0 then neg = true end
    end
    if pos and not neg then return true end
    if neg and not pos then return true end
    -- linear f = a·k + b·p + c·q + d:  extrema of D sit at the
    -- vertex (1,0,1) and the recession cone's extreme rays
    -- (1,0,0), (1,1,0), (1,0,1)
    if f.k2 == 0 and f.q2 == 0 and (f.p2 or 0) == 0
       and f.kq == 0 and (f.kp or 0) == 0 and (f.pq or 0) == 0 then
        local a, b, c, d = f.k, f.p or 0, f.q, f.c
        if a >= 0 and a + b >= 0 and a + c >= 0
           and a + c + d > 0 then return true end
        if a <= 0 and a + b <= 0 and a + c <= 0
           and a + c + d < 0 then return true end
    end
    return each_domain_point(legal, function(k, p, q)
        if poly_eval(f, k, p, q) == 0 then
            return { k = k, p = p, q = q }
        end
    end)
end
nz_domain = function(f, legal)
    local mn = common_monomial(f)
    -- a common p-factor means f = 0 at p = 0 — a real domain point
    if mn[2] > 0 then return { k = 1, p = 0, q = 1 } end
    return nz_raw(divide_monomial(f, mn), legal)
end

-- is f ≥ 0 for all legal domain points?  (same contract)
local function gez_raw(f, legal)
    if poly_zero(f) then return true, "identity" end
    local pos, neg = false, false
    for _, t in ipairs(POLY_KEYS) do
        if (f[t] or 0) > 0 then pos = true
        elseif (f[t] or 0) < 0 then neg = true end
    end
    if not neg then return true end
    if f.k2 == 0 and f.q2 == 0 and (f.p2 or 0) == 0
       and f.kq == 0 and (f.kp or 0) == 0 and (f.pq or 0) == 0 then
        local a, b, c, d = f.k, f.p or 0, f.q, f.c
        if a >= 0 and a + b >= 0 and a + c >= 0
           and a + c + d >= 0 then return true end
    end
    return each_domain_point(legal, function(k, p, q)
        if poly_eval(f, k, p, q) < 0 then
            return { k = k, p = p, q = q }
        end
    end)
end
gez_domain = function(f, legal)
    return gez_raw(divide_monomial(f, common_monomial(f)), legal)
end

-- i(k,q) = A·q + B·k + C — a LINEAR poly (constants and k,q terms;
-- also p allowed: i may depend on the whole split)
local function parse_iexpr(s)
    s = (s or ""):gsub("%s", "")
    if s == "" then return nil end
    if s:find("-") then return nil end   -- i ≥ 0 required anyway
    local r = parse_exp(s)               -- parentheses allowed
    if not r then return nil end
    if r.k < 0 or r.p < 0 or r.q < 0 or r.c < 0 then return nil end
    return r
end
local function iexpr_eval(i, k, p, q)
    return i.c + i.k * k + (i.p or 0) * p + i.q * q
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
-- GEN[lang](pb, legal):  pb = pumped merged block list
-- {sym, poly={c,k,p,q,...}};  legal(k,p,q) filters to the student's
-- legal splits.  -> true (proven ∉ L) | {k,p,q} counterexample |
-- nil (cannot decide — caller warns)
local GEN = {}

local function poly_add(a, b)
    local r = {}
    for _, t in ipairs(POLY_KEYS) do r[t] = (a[t] or 0) + (b[t] or 0) end
    return r
end

-- eq_ab:  Σ ±exp must be ≠ 0 on the whole legal domain
GEN.eq_ab = function(pb, legal)
    local diff = poly{}
    for _, b in ipairs(pb) do
        diff = poly_add(diff,
            poly_scale(b.poly, b.sym == "a" and 1 or -1))
    end
    return nz_domain(diff, legal)
end

-- parens:  total balance ≠ 0, or some block-boundary prefix dips
-- below 0, on the whole legal domain
GEN.parens = function(pb, legal)
    local bal = poly{}
    for _, b in ipairs(pb) do
        bal = poly_add(bal,
            poly_scale(b.poly, b.sym == "(" and 1 or -1))
    end
    if nz_domain(bal, legal) == true then return true end
    -- try a boundary dip: balance after block j stays < 0 everywhere
    local acc = poly{}
    for j = 1, #pb - 1 do
        acc = poly_add(acc,
            poly_scale(pb[j].poly,
                       pb[j].sym == "(" and 1 or -1))
        -- need acc ≤ −1 on all legal points
        local neg1 = poly_sub(poly_scale(acc, -1), poly{ c = 1 })
        if gez_domain(neg1, legal) == true then return true end
    end
    return nil
end

-- palindrome:  some mirror pair must mismatch everywhere
GEN.pal = function(pb, legal)
    if #pb < 2 then return nil end
    for j = 1, math.floor(#pb / 2) do
        local f, s = pb[j], pb[#pb + 1 - j]
        if f.sym ~= s.sym then return true end
        local diff = poly_sub(f.poly, s.poly)
        if nz_domain(diff, legal) == true then return true end
    end
    return nil
end

-- {a^n b^m | n<m}:  pumped must break the a·b shape or n' ≥ m'
GEN.anbm_lt = function(pb, legal)
    if #pb ~= 2 or pb[1].sym ~= "a" or pb[2].sym ~= "b" then
        if #pb == 1 then return nil end   -- all-a/b still in L
        return true                       -- shape broken -> out
    end
    local g = poly_sub(pb[1].poly, pb[2].poly)
    return gez_domain(g, legal)
end

-- {a^i b^j c^{2j}}:  pumped must satisfy #c ≠ 2·#b on any
-- a*·b*·c* shape (a or b blocks may have collapsed to nothing)
GEN.aibjc = function(pb, legal)
    local order = { a = 1, b = 2, c = 3 }
    local prev = 0
    for _, b in ipairs(pb) do
        local o = order[b.sym]
        if not o or o < prev then return true end   -- shape broken
        prev = o
    end
    -- all-a word: a^i is always in L — cannot prove out
    if #pb == 1 and pb[1].sym == "a" then return nil end
    local cb, bb = poly{}, poly{}
    for _, b in ipairs(pb) do
        if b.sym == "c" then cb = poly_add(cb, b.poly) end
        if b.sym == "b" then bb = poly_add(bb, b.poly) end
    end
    local g = poly_sub(cb, poly_scale(bb, 2))
    return nz_domain(g, legal)
end

-- {ww}:  length odd everywhere, or the halves differ everywhere
GEN.ww = function(pb, legal)
    local len = poly{}
    for _, b in ipairs(pb) do len = poly_add(len, b.poly) end
    local var_odd = false
    for _, t in ipairs(POLY_KEYS) do
        if t ~= "c" and len[t] % 2 ~= 0 then var_odd = true end
    end
    if not var_odd and len.c % 2 == 1 then return true end
    -- symbolic half-split (formal halves; odd-length points are out
    -- anyway, so it suffices to prove mismatch on the whole domain)
    local H = poly_scale(len, 0.5)
    local C, first, second, j = poly{}, {}, {}, 1
    while j <= #pb do
        local b = pb[j]
        local nj = poly_add(C, b.poly)
        local D = poly_sub(nj, H)
        local nonpos = gez_domain(poly_scale(D, -1), legal)
        local nonneg = gez_domain(D, legal)
        if nonpos == true then
            first[#first + 1] = b
            if poly_zero(D) then
                for m = j + 1, #pb do
                    second[#second + 1] = pb[m]
                end
                break
            end
            C, j = nj, j + 1
        elseif nonneg == true or nonneg == nil then
            local e1 = poly_sub(H, C)
            local tail = poly_sub(b.poly, e1)
            first[#first + 1] = { sym = b.sym, poly = e1 }
            if not poly_zero(tail) then
                second[#second + 1] = { sym = b.sym, poly = tail }
            end
            for m = j + 1, #pb do second[#second + 1] = pb[m] end
            break
        else
            return nil
        end
    end
    if #first ~= #second then return true end
    for m = 1, #first do
        local f, s = first[m], second[m]
        if f.sym ~= s.sym then return true end
        local diff = poly_sub(f.poly, s.poly)
        if nz_domain(diff, legal) == true then return true end
    end
    return nil
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

-- full general check over the STUDENT-written decomposition
--   gen = { u = "a^p", v = "a^q", w = "a^{k-p-q}b^k", i = "2",
--           pw = "a^{k+q}b^k", why = "<reason option id>" }
-- verified: uvw ≡ z(k) as a poly identity, legality |v| ≥ 1 /
-- |uv| ≤ k on the legal domain, coverage of every legal split,
-- the pumped word uv^iw ≡ pw as a pattern, the reason, and
-- uv^iw ∉ L — symbolically where possible, else sampled.
-- returns nil when the witness has no closed-form step at all
-- (first block does not dominate) and nothing was filled in.
function M.check_general(lang_id, z_str, gen, part)
    gen = gen or {}
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
    -- the closed-form step exists only when z's first block
    -- dominates the first-k window; then it is required — the
    -- schema is the proof, not an optional extra
    local filled = (gen.u or ""):match("%S") or (gen.v or ""):match("%S")
        or (gen.w or ""):match("%S") or (gen.i or ""):match("%S")
        or (gen.pw or ""):match("%S") or (gen.why or ""):match("%S")
    if not filled then
        if gcase.err then return nil end
        return { ok = false, kind = "fail",
                 msg = "the general step is missing — write u, v, w "
                    .. "as patterns (step 2) and choose i, the "
                    .. "pumped word and the reason (step 3)" }
    end
    if gcase.err then
        return { ok = false, kind = "fail", msg = gcase.err }
    end
    local ub, uerr = M.parse_pattern_pq(gen.u or "")
    if not ub then return { ok = false, kind = "fail",
                            msg = "u: " .. uerr } end
    local vb, verr2 = M.parse_pattern_pq(gen.v or "")
    if not vb then return { ok = false, kind = "fail",
                            msg = "v: " .. verr2 } end
    local wb, werr = M.parse_pattern_pq(gen.w or "")
    if not wb then return { ok = false, kind = "fail",
                            msg = "w: " .. werr } end
    if #vb ~= 1 then
        return { ok = false, kind = "fail",
                 msg = "v must be a single block — inside the "
                    .. "first block of z every v is " .. gcase.sym
                    .. "^q anyway" }
    end
    local iexpr = parse_iexpr(gen.i or "")
    if not iexpr then
        return { ok = false, kind = "fail",
                 msg = "i must be a non-negative integer or an "
                    .. "expression in k, p, q (e.g. 2, 0, q+1, k+1)" }
    end

    -- (1) uvw ≡ z(k):  merged concatenation must equal z's merged
    --     list — same symbols, identical exponent polys
    local cat = {}
    for _, b in ipairs(ub) do cat[#cat + 1] = b end
    for _, b in ipairs(vb) do cat[#cat + 1] = b end
    for _, b in ipairs(wb) do cat[#cat + 1] = b end
    local cm = merge(dropzero(cat))
    if #cm ~= #mb then
        return { ok = false, kind = "fail",
                 msg = "uvw has " .. #cm .. " block(s), z has " .. #mb
                    .. " — the decomposition does not reassemble "
                    .. "into z(k)" }
    end
    for j = 1, #mb do
        if cm[j].sym ~= mb[j].sym then
            return { ok = false, kind = "fail",
                     msg = "uvw's block " .. j .. " is '"
                        .. cm[j].sym .. "', z's is '" .. mb[j].sym
                        .. "'" }
        end
        local d = poly_sub(block_poly(cm[j]), block_poly(mb[j]))
        if not poly_zero(d) then
            return { ok = false, kind = "fail",
                     msg = "block " .. j .. ": exponents differ — "
                        .. "uvw ≢ z(k) as an identity" }
        end
    end

    -- the student's legal domain: every exponent ≥ 0, |v| ≥ 1,
    -- |uv| ≤ k — derived from their expressions
    local ulen = poly{}
    for _, b in ipairs(ub) do ulen = poly_add(ulen, block_poly(b)) end
    local vlen = block_poly(vb[1])
    local uvlen = poly_add(ulen, vlen)
    local legal = function(k, p, q)
        for _, bl in ipairs(cm) do
            if poly_eval(block_poly(bl), k, p, q) < 0 then
                return false
            end
        end
        if poly_eval(vlen, k, p, q) < 1 then return false end
        if poly_eval(uvlen, k, p, q) > k then return false end
        return true
    end

    -- (2) legality must allow at least the standard splits — check
    --     v ≥ 1 possible and uv ≤ k possible somewhere
    local any_legal = false
    for k = 1, 8 do
        for p = 0, k do
            for q = 1, k - p do
                if legal(k, p, q) then any_legal = true end
            end
        end
    end
    if not any_legal then
        return { ok = false, kind = "fail",
                 msg = "your decomposition allows no legal split "
                    .. "at all (|v| ≥ 1 and |uv| ≤ k never both "
                    .. "hold)" }
    end

    -- (3) coverage: every legal split at k = 3, 4 must be reachable
    --     by some (p,q) — catches parametrisations that bind p to q
    for K = 3, 4 do
        for pc = 0, K - 1 do
            for qc = 1, K - pc do
                local covered = false
                for p = 0, K do
                    for q = 1, K - p do
                        if legal(K, p, q)
                           and poly_eval(ulen, K, p, q) == pc
                           and poly_eval(vlen, K, p, q) == qc then
                            covered = true
                        end
                    end
                end
                if not covered then
                    return { ok = false, kind = "fail",
                        msg = "your decomposition cannot express the "
                           .. "legal split u = " .. gcase.sym .. "^"
                           .. pc .. ", v = " .. gcase.sym .. "^" .. qc
                           .. " (e.g. at k=" .. K
                           .. ") — keep the parameters free" }
                end
            end
        end
    end

    -- (4) concrete counterexample scan on the legal domain
    for k = 1, 8 do
        for p = 0, k do
            for q = 1, k - p do
                if legal(k, p, q) then
                    local i = iexpr_eval(iexpr, k, p, q)
                    if i == math.floor(i) and i >= 0 then
                        local us = M.expand_params(ub, k, p, q)
                        local vs = M.expand_params(vb, k, p, q)
                        local ws = M.expand_params(wb, k, p, q)
                        local pumped = us .. vs:rep(i) .. ws
                        if lang.mem(pumped) then
                            return { ok = false, kind = "fail",
                                msg = "counterexample at k=" .. k
                                    .. ", p=" .. p .. ", q=" .. q
                                    .. ":  uv^" .. i .. "w = "
                                    .. pumped .. " ∈ L" }
                        end
                    end
                end
            end
        end
    end

    -- (5) symbolic proof: pumped merged block list with poly exps
    local vi = poly_mul(block_poly(vb[1]), iexpr)
    local cat2 = {}
    for _, b in ipairs(ub) do
        cat2[#cat2 + 1] = { sym = b.sym, poly = block_poly(b) }
    end
    cat2[#cat2 + 1] = { sym = vb[1].sym, poly = vi }
    for _, b in ipairs(wb) do
        cat2[#cat2 + 1] = { sym = b.sym, poly = block_poly(b) }
    end
    local pb = {}
    for _, b in ipairs(cat2) do
        local top = pb[#pb]
        if top and top.sym == b.sym then
            top.poly = poly_add(top.poly, b.poly)
        else
            pb[#pb + 1] = { sym = b.sym, poly = b.poly }
        end
    end

    -- (5b) 'Then uv^i w = …' — the student's pumped word must equal
    --     u·v^i·w as a pattern over the legal domain.  A linear
    --     pattern in k, p, q can express it only when i is
    --     constant; with a parameter-dependent i the exponent is
    --     quadratic, so the field is optional (but still checked)
    --     in that case.
    local iconst = iexpr.k == 0 and (iexpr.p or 0) == 0
        and iexpr.q == 0
    if (gen.pw or ""):match("%S") then
        local pwb, pwerr = M.parse_pattern_pq(gen.pw)
        if not pwb then
            return { ok = false, kind = "fail",
                     msg = "uv^i w = " .. pwerr }
        end
        -- zero-exponent blocks contribute nothing (v^0, a^{0q},
        -- stray λ-annotated pieces) — drop them on both sides
        local pmz, pbz = dropzero(merge(pwb)), {}
        for _, b in ipairs(pb) do
            if not poly_zero(b.poly) then pbz[#pbz + 1] = b end
        end
        local bad = (#pmz ~= #pbz) and "block count differs"
        for j = 1, #pbz do
            if not bad
               and (pmz[j].sym ~= pbz[j].sym
                    or not poly_zero(poly_sub(block_poly(pmz[j]),
                                              pbz[j].poly))) then
                bad = "block " .. j .. " differs"
            end
        end
        if bad then
            local cx = each_domain_point(legal, function(k, p, q)
                local ii = iexpr_eval(iexpr, k, p, q)
                if ii ~= math.floor(ii) or ii < 0 then return nil end
                local truth = M.expand_params(ub, k, p, q)
                    .. (M.expand_params(vb, k, p, q)):rep(ii)
                    .. M.expand_params(wb, k, p, q)
                local got = M.expand_params(pmz, k, p, q)
                if got ~= truth then
                    return { k = k, p = p, q = q,
                             truth = truth, got = got }
                end
            end)
            local msg = "your 'uv^i w =' does not equal u·v^i·w"
            if cx then
                msg = msg .. " — e.g. at k=" .. cx.k .. ", p="
                    .. cx.p .. ", q=" .. cx.q .. ":  u·v^i·w = '"
                    .. cx.truth .. "', your pattern gives '"
                    .. cx.got .. "'"
            end
            if not iconst then
                msg = msg .. "  (with a parameter-dependent i the "
                    .. "pumped word is not a linear pattern in "
                    .. "k, p, q — a constant i is usually what the "
                    .. "proof wants)"
            end
            return { ok = false, kind = "fail", msg = msg }
        end
    elseif iconst then
        return { ok = false, kind = "fail",
                 msg = "state the pumped word:  uv^i w = ?" }
    end

    -- (5c) the reason: which defining property of L does the
    --     pumped word violate?  options are authored per task;
    --     the checker just verifies the pick
    local want_why = part and part.why and part.why.correct
    if want_why then
        if not (gen.why or ""):match("%S") then
            return { ok = false, kind = "fail",
                     msg = "state why uv^iw ∉ L — which defining "
                        .. "property of L does the pumped word "
                        .. "violate?" }
        elseif gen.why ~= want_why then
            return { ok = false, kind = "fail",
                     msg = "that is not the reason uv^iw leaves L "
                        .. "— which defining property of L fails?" }
        end
    end

    local prov = lang.gen and lang.gen(pb, legal)
    if prov == true then
        return { ok = true, kind = "ok",
                 msg = "uvw ≡ z(k), all splits covered, and uv^iw ∉ L "
                    .. "for all k ≥ 1 — verified symbolically" }
    elseif type(prov) == "table" and prov.k then
        return { ok = false, kind = "fail",
                 msg = prov.msg or ("counterexample at k=" .. prov.k
                       .. (prov.p and (", p=" .. prov.p) or "")
                       .. ", q=" .. tostring(prov.q)) }
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
function M.check(lang_id, z_str, is_tbl, K, gen, part)
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
    -- the general decomposition (all k): student-written u, v, w,
    -- i, pumped word and reason — required whenever the witness
    -- admits a closed form (check_general returns nil otherwise)
    local genres = M.check_general(lang_id, z_str, gen, part)
    if genres and not genres.ok then all_ok = false end
    if all_ok then
        return { ok = true, kind = "ok", rows = rows,
                 gen = genres, msg = "z(k) ∈ L, |z| ≥ k, and every decomposition "
                    .. "is beaten — the pumping argument works (k="
                    .. K .. ")" }
    end
    return { ok = false, kind = "fail", rows = rows,
             gen = genres, msg = "every split (u,v,w) needs an i with uv^iw ∉ L" }
end

return M
