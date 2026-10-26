-- automata/label_lang.lua — LPeg transition-label grammars per
-- automaton type.  Single source of truth shared by the graphical
-- automaton editor (server/checks.lua validates labels live) and the
-- wordproof graders (model JSON -> machine objects).
--
-- A label on ONE edge describes ONE transition.  λ stands for the
-- empty word (input), "no pop"/"no push" (PDA) and the blank/keep
-- (TM read/write; "~" keeps the cell contents too).  Accepted shapes:
--
--   pda   "a A/AA" | "a, A -> AA" | "a, A → AA" | "λ Z/Z"
--   tm    "a b R"  | "a,b,R"      | "a -> b, R"  | "a b -> R"
--   tm-N  "a b R | B B L"        — N clauses separated by '|'
--
-- parse(type, label) returns a plain tuple table or nil, reason:
--   pda   -> {input=sym|"", pop=sym|"", push=string|""}
--   tm    -> {r=sym, w=sym|nil (keep), d="L"|"R"|"S"}
--   tm-N  -> { {r,w,d}, ... } with exactly N clauses
local lpeg = require "lpeg"
local M = {}

local P, S, C, Ct = lpeg.P, lpeg.S, lpeg.C, lpeg.Ct
local sp   = S" \t"^0
local EOL  = P(-1)
local LAM  = P"λ" + P"ε" + P"eps" + P"\\lambda"
-- a symbol token: maximal run excluding separators/ws
local ID   = C((1 - S" \t,;/|→")^1)
local LAMC = C(LAM)
local SEP1 = (sp * P"," * sp) + (S" \t"^1)
local ARR  = sp * (P"→" + P"->") * sp
local SLASH= sp * P"/" * sp
local DIR  = C(S"LRS")

local function unlam(s)
    if not s then return "" end
    s = s:gsub("λ+", ""):gsub("ε+", "")
    if s == "eps" or s == "\\lambda" then return "" end
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
    C(P(1)^0) * sp * EOL                -- push = rest

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
        if t[1] == "λ" or t[1] == "ε" then t[1] = "B" end    -- λ=B
        if t[2] == "λ" or t[2] == "ε" or t[2] == "~"
           or t[2] == "eps" or t[2] == "\\lambda" then
            t[2] = nil                                     -- λ/~ keep
        end
    end
    return ts
end

-- ---------- registry ----------
function M.tapes(atype)
    local n = (atype or ""):match("^tm%-(%d+)$")
    if n then return tonumber(n) end
    if atype == "tm" then return 1 end
    return nil
end

-- does the type use structured (non-symbol-list) labels?
function M.is_structured(atype)
    return atype == "pda" or M.tapes(atype) ~= nil
end

-- parse(type, label) -> tuple | nil, reason
function M.parse(atype, label)
    if atype == "pda" then return parse_pda(label) end
    local n = M.tapes(atype)
    if n then return parse_tm(label, n) end
    return nil, "no label grammar for type '" .. tostring(atype) .. "'"
end

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
