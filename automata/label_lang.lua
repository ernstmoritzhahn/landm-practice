-- automata/label_lang.lua — LPeg transition-label grammars per
-- automaton type.  Single source of truth shared by the graphical
-- automaton editor (server/checks.lua validates labels live) and the
-- wordproof graders (model JSON -> machine objects).
--
-- A label on ONE edge describes ONE transition.  λ stands for the
-- empty word (input), "no pop"/"no push" (PDA) and "keep" (TM write;
-- "~" too).  The TM blank is "⊔" ("B" accepted as the book's
-- notation); λ is NOT the blank.  Accepted shapes:
--
--   pda   "a A/AA" | "a, A -> AA" | "a, A → AA" | "λ Z/Z"
--         (same grammar for all pda-family types: pda, pda-f, pda-e,
--         dpda, dpda-f, dpda-e — the suffix picks the acceptance mode)
--   tm    "a b R"  | "a,b,R"      | "a -> b, R"  | "a b -> R"
--   tm-N  "a b R | ⊔ ⊔ L"        — N clauses separated by '|'
--         (ntm/ntm-N are the nondeterministic TM variants, same
--         clause grammar)
--
-- parse(type, label) returns a plain tuple table or nil, reason:
--   pda   -> {input=sym|"", pop=sym|"", push=string|""}
--   tm    -> {r=sym, w=sym|nil (keep), d="L"|"R"|"S"}
--   tm-N  -> { {r,w,d}, ... } with exactly N clauses
local lpeg = require "lpeg"
-- no lib.util dependency: this file is also staged into the
-- editor's wasm VFS, which does not carry lib/ — keep it standalone
local function split(str, sep)
    local out, i = {}, 1
    while true do
        local a, b = str:find(sep, i, true)
        if not a then break end
        out[#out + 1] = str:sub(i, a - 1)
        i = b + 1
    end
    out[#out + 1] = str:sub(i)
    return out
end
local function trim(s)
    return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end
local M = {}

local P, S, C, Ct = lpeg.P, lpeg.S, lpeg.C, lpeg.Ct
local sp   = S" \t"^0
local EOL  = P(-1)
local LAM  = P"λ" + P"ε" + P"eps" + P"\\lambda" + P"\\lamda"
-- a symbol token: maximal run excluding separators/ws and "→"
-- (multibyte: putting → into the S-set would ban every symbol whose
-- UTF-8 shares a byte with it — ⊔ = E2 8A 94 vs → = E2 86 92)
local ID   = C(((1 - S" \t,;/|") - P"→")^1)
local LAMC = C(LAM)
local SEP1 = (sp * P"," * sp) + (S" \t"^1)
local ARR  = sp * (P"→" + P"->") * sp
local SLASH= sp * P"/" * sp
local DIR  = C(S"LRS")

local function unlam(s)
    if not s then return "" end
    s = s:gsub("λ+", ""):gsub("ε+", "")
    if s == "eps" or s == "\\lambda" or s == "\\lamda" then return "" end
    return s
end

-- ---------- pda ----------
-- input POP/PUSH with the op between pop and push; input and pop are
-- each a single symbol (or λ), push is the rest of the label
local pda_patt =
    sp * (LAMC + ID) *                  -- input
    SEP1 *
    (LAMC + ID) *                       -- pop
    (ARR + SLASH) *
    -- push = symbol string; must not swallow a following clause —
    -- ',' and ';' start the next label on the same edge
    C((1 - S" \t,;/|")^0) * sp * EOL

local function parse_pda(label)
    local i, p, u = pda_patt:match(label or "")
    if not i then
        return nil, "want 'input pop/push' or 'input, pop -> push'"
    end
    return { input = unlam(i), pop = unlam(p), push = unlam(u) }
end

-- ---------- tm ----------
-- read WRITE DIR — separators whitespace/comma/arrow, dir one of LRS;
-- each clause captures into its own {r,w,d} table
local TSEP = (sp * (P"," + P"→" + P"->") * sp) + (S" \t"^1)
local tm_clause = Ct(sp * (LAMC + ID) * TSEP *
                     (LAMC + ID + C(P"~")) * TSEP * DIR * sp)
local tm_patt = Ct(tm_clause * (P"|" * tm_clause)^0) * EOL

local function parse_tm(label, ntapes)
    local ts = tm_patt:match(label or "")
    if not ts or #ts == 0 then
        return nil, "want 'read write L|R|S'"
            .. (ntapes > 1 and (" (×" .. ntapes .. ", '|'-separated)")
                or "")
    end
    if #ts ~= ntapes then
        return nil, "expected " .. ntapes .. " tape clause(s), got "
            .. #ts
    end
    for _, t in ipairs(ts) do
        -- blank: ⊔ is the course notation, B the book's alias
        if t[1] == "⊔" or t[1] == "B" then t[1] = "B" end
        if t[2] == "⊔" or t[2] == "B" then t[2] = "B" end
        if t[1] == "λ" or t[1] == "ε"
           or t[1] == "eps" or t[1] == "\\lambda"
           or t[1] == "\\lamda" then
            return nil, "λ is not the blank — use ⊔"
        end
        if t[2] == "λ" or t[2] == "ε" or t[2] == "~"
           or t[2] == "eps" or t[2] == "\\lambda"
           or t[2] == "\\lamda" then
            t[2] = nil                                     -- λ/~ keep
        end
    end
    return ts
end

-- one edge may carry several comma- or semicolon-separated labels
-- (the book draws "b A/λ; b λ/λ" on a single edge).  ';' always
-- separates; a bare ',' separates too when the unsplit segment does
-- not parse as one clause (so "a, A -> AA" stays a single clause).
local function parse_many(atype, label)
    local segs = {}
    for _, s in ipairs(split(label or "", ";")) do
        s = trim(s)
        if s ~= "" then segs[#segs + 1] = s end
    end
    if #segs == 0 then
        return nil, "want 'input pop/push' — one or more "
            .. "comma/semicolon-separated clauses"
    end
    local out = {}
    for _, seg in ipairs(segs) do
        local t, why = M.parse(atype, seg)
        if t then
            out[#out + 1] = t
        elseif seg:find(",") then
            -- comma-separated space-form clauses ("b A/λ,b λ/λ"):
            -- every piece must parse as a full clause
            for _, cs in ipairs(split(seg, ",")) do
                if trim(cs) ~= "" then
                    local ct, cw = M.parse(atype, cs)
                    if not ct then
                        return nil, "'" .. trim(cs)
                            .. "': " .. tostring(cw)
                    end
                    out[#out + 1] = ct
                end
            end
        else
            return nil, "'" .. seg .. "': " .. tostring(why)
        end
    end
    return out
end

-- ---------- registry ----------
-- type families: the PDA family is pda|pda-f|pda-e (nondeterministic)
-- plus dpda|dpda-f|dpda-e (deterministic); the suffix picks the
-- acceptance mode — -f final state only (L_F), -e empty stack only
-- (L_E), no suffix = both (the lecture's plain L(M)).  The TM family
-- is tm|tm-N (deterministic) and ntm|ntm-N (nondeterministic).
function M.is_pda(atype)
    return atype ~= nil and atype:match("^d?pda") ~= nil
end

function M.is_det_pda(atype)
    return atype ~= nil and atype:match("^dpda") ~= nil
end

-- "fe" | "f" | "e"
function M.pda_accept(atype)
    local s = (atype or ""):match("%-(%l+)$")
    return (s == "f" or s == "e") and s or "fe"
end

function M.tapes(atype)
    local n = (atype or ""):match("^n?tm%-(%d+)$")
    if n then return tonumber(n) end
    if atype == "tm" or atype == "ntm" then return 1 end
    return nil
end

-- deterministic TM variants (tm, tm-N) vs nondeterministic (ntm*)
function M.is_det_tm(atype)
    return atype ~= nil and atype:match("^tm") ~= nil
end

-- does the type use structured (non-symbol-list) labels?
function M.is_structured(atype)
    return M.is_pda(atype) or M.tapes(atype) ~= nil
end

-- parse(type, label) -> tuple | nil, reason
function M.parse(atype, label)
    if M.is_pda(atype) then return parse_pda(label) end
    local n = M.tapes(atype)
    if n then return parse_tm(label, n) end
    return nil, "no label grammar for type '" .. tostring(atype) .. "'"
end

-- parse_many(type, label) -> {tuple,...} | nil, reason — one edge
-- may carry several ','/';'-separated transition labels
M.parse_many = parse_many

-- canonical "input pop/push" string for pda:add_transition
function M.pda_label(t)
    local function orlam(s) return s ~= "" and s or "λ" end
    return orlam(t.input) .. " " .. orlam(t.pop) .. "/" .. orlam(t.push)
end

-- tape clause -> {r=, w=, d=} record (w nil keeps the symbol)
function M.tm_clause(t)
    return { r = t[1], w = t[2], d = t[3] }
end

return M
