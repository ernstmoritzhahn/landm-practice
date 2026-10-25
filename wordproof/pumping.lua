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

M.LANGS = {
    eq_ab    = { label = "{w ∈ {a,b}* | #a(w) = #b(w)}",
                 valid = VALID.eq_ab, mem = MEM.eq_ab },
    parens   = { label = "matched parentheses over {(,)}",
                 valid = VALID.parens, mem = MEM.parens },
    pal      = { label = "palindromes over {a,b}",
                 valid = VALID.pal, mem = MEM.pal },
    ww       = { label = "{ww | w ∈ {a,b}*}",
                 valid = VALID.ww, mem = MEM.ww },
    anbm_lt  = { label = "{a^n b^m | n < m}",
                 valid = VALID.anbm_lt, mem = MEM.anbm_lt },
    aibjc    = { label = "{a^i b^j c^{2j}}",
                 valid = VALID.aibjc, mem = MEM.aibjc },
}

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
    return { word = z, splits = M.splits(z, K), k = K }
end

-- full check: z valid + every split row has a working i.
-- is_tbl[ri] = the student's pumping index for split row ri.
function M.check(lang_id, z_str, is_tbl, K)
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
    if all_ok then
        return { ok = true, kind = "ok", rows = rows,
                 msg = "z(k) ∈ L, |z| ≥ k, and every decomposition "
                    .. "is beaten — the pumping argument works (k="
                    .. K .. ")" }
    end
    return { ok = false, kind = "fail", rows = rows,
             msg = "every split (u,v,w) needs an i with uv^iw ∉ L" }
end

return M
