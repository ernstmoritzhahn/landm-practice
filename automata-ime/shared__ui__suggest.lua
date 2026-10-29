-- ui/suggest.lua -- suggestion-bar vocabulary: the digit/letter
-- on-screen-keyboard rows and the syn syntax-class tables (keywords,
-- builtins, operators; palette + editor span classifier).  Pure text
-- utilities plus data -- nothing here touches E, the bridge or the
-- network, so the module loads under any target.

local ffi = require "ffi"

local suggest = {}

-- Number-entry helpers for the on-screen digit row.  The row appears
-- whenever the parser explicitly expects <number> or the caret touches
-- an existing number token, so a complete "5" can still be extended to
-- "55" or "5.3".  Dot and minus are gated by the partial token: dot only
-- once per number and only after at least one digit; minus only to start
-- a fresh number.

local digit = {
    tokens = {"1","2","3","4","5","6","7","8","9","0"},
    dot = ".",
    minus = "-"
}

function digit.is_utf8_cont(b)
    return b ~= nil and b >= 0x80 and b <= 0xBF
end

function digit.prev_rune_start(text, p)
    if p < 1 then return nil end
    local q = p
    while q >= 2 and digit.is_utf8_cont(text:byte(q)) do q = q - 1 end
    return q
end

function digit.rune_at(text, p)
    if p < 1 or p > #text then return nil end
    local r = p
    while r + 1 <= #text and digit.is_utf8_cont(text:byte(r + 1)) do
        r = r + 1
    end
    return text:sub(p, r)
end

function digit.prev_nonspace_rune(text, p)
    local q = p
    while q >= 1 and text:sub(q, q):match("%s") do q = q - 1 end
    if q < 1 then return nil, nil end
    local qs = digit.prev_rune_start(text, q)
    return qs, digit.rune_at(text, qs)
end

function digit.is_operand_rune(rune)
    return rune and rune:match("^[%d%a_.%)%]]$") ~= nil
end

function digit.is_valid_number_prefix(s)
    if s == "" then return false end
    if s == "-" then return true end
    return s:match("^%-?%d+%.?%d*$") ~= nil
end

function digit.number_token_at(text, to)
    -- Return the partial number token ending at to-1 plus dot/minus/digit
    -- flags.  The token is the contiguous digits/"."/leading "-" suffix
    -- that the caret is part of.
    local empty = {token = "", has_minus = false, has_dot = false,
                   has_digit = false}
    if not text or not to or to < 1 then return empty end
    local n = #text
    local p = math.min(to - 1, n)
    local has_dot = false
    local has_digit = false
    while p >= 1 do
        local c = text:sub(p, p)
        if c:match("%d") then
            has_digit = true
            p = p - 1
        elseif c == "." then
            if has_dot then break end
            has_dot = true
            p = p - 1
        elseif c == "-" then
            local _, prev = digit.prev_nonspace_rune(text, p - 1)
            if not prev or digit.is_operand_rune(prev) then
                break
            end
            return {token = text:sub(p, to - 1), has_minus = true,
                    has_dot = has_dot, has_digit = has_digit}
        else
            break
        end
    end
    local token = text:sub(p + 1, to - 1)
    has_digit = token:match("%d") ~= nil
    return {token = token, has_minus = false, has_dot = has_dot,
            has_digit = has_digit}
end

function digit.digit_row_allowed(text, expected, from, to)
    if expected then
        for _, t in ipairs(expected) do
            if tostring(t) == "<number>" then return true end
        end
    end
    if text and from and to then
        local tok = digit.number_token_at(text, to)
        return digit.is_valid_number_prefix(tok.token)
    end
    return false
end

function digit.digit_row_tokens(text, expected, from, to)
    -- Build the digit row, or nil when no digit row should be shown.
    if not digit.digit_row_allowed(text, expected, from, to) then
        return nil
    end
    local tok = digit.number_token_at(text, to)
    local row = {}
    for _, d in ipairs(digit.tokens) do row[#row + 1] = d end
    if tok.has_digit and not tok.has_dot then
        row[#row + 1] = digit.dot
    end
    if tok.token == "" then
        local ps, prev = digit.prev_nonspace_rune(text, to - 1)
        local allow_minus = true
        if prev == "-" and ps then
            local _, pprev = digit.prev_nonspace_rune(text, ps - 1)
            if not pprev or not digit.is_operand_rune(pprev) then
                allow_minus = false
            end
        elseif prev and digit.is_operand_rune(prev) then
            allow_minus = false
        end
        if allow_minus then row[#row + 1] = digit.minus end
    end
    return row
end

-- Letter-entry helpers for the on-screen keyboard row.  The row appears
-- while a fresh binding name can be typed (the "<name>" marker — the
-- LET name slot), so the name is not limited to the one suggestion.
-- A name may continue with digits but never start with one, so digits
-- join the row only while the caret is already inside a name token.

local letter = {}
letter.alphabet = {}
for i = 0, 25 do letter.alphabet[#letter.alphabet + 1] = string.char(97 + i) end
for i = 0, 25 do letter.alphabet[#letter.alphabet + 1] = string.char(65 + i) end
letter.alphabet[#letter.alphabet + 1] = "_"

-- the identifier token ending exactly at byte to-1 ("" when the caret
-- is not on an identifier)
function letter.ident_token_at(text, to)
    if not text or not to or to < 2 then return "" end
    local p = math.min(to - 1, #text)
    while p >= 1 and text:sub(p, p):match("[%a%d_]") do p = p - 1 end
    return text:sub(p + 1, to - 1)
end

-- whether the caret sits inside/at the end of a binding name that may
-- still grow — the keyword spellings themselves do not count (a letter
-- appended to "LET" would fuse into a new identifier, not a name)
function letter.name_being_typed(text, to)
    local tok = letter.ident_token_at(text, to)
    return tok ~= "" and tok ~= "LET" and tok ~= "IN" and tok ~= "DO"
end

function letter.row_allowed(text, expected, from, to)
    if expected then
        for _, t in ipairs(expected) do
            if tostring(t) == "<name>" then return true end
        end
    end
    return false
end

function letter.row_tokens(text, expected, from, to)
    if not letter.row_allowed(text, expected, from, to) then
        return nil
    end
    local row = {}
    for _, ch in ipairs(letter.alphabet) do row[#row + 1] = ch end
    if letter.name_being_typed(text, to) then
        for _, d in ipairs(digit.tokens) do row[#row + 1] = d end
    end
    return row
end

-- ---------------------------------------------------------------------
-- syntax classes for the suggestion buttons — the same classes the C
-- formula editor uses for highlighting: model node names are variables,
-- their outcome names (except numbers) enum literals, LET-bound names
-- count as variables too.  Keeping the palette consistent between the
-- editor text and the bar makes a legal token recognisable at a glance.
local syn = {}

syn.kw = {
    ["¬"]=1, ["∧"]=1, ["∨"]=1, ["↑"]=1, ["↓"]=1, ["→"]=1, ["↔"]=1, ["⊕"]=1,
    ["!"]=1, ["&&"]=1, ["||"]=1, ["->"]=1, ["<->"]=1,
    ["not"]=1, ["and"]=1, ["nand"]=1, ["or"]=1, ["nor"]=1,
    ["implication"]=1, ["biimplication"]=1, ["xor"]=1,
    LET=1, DO=1, IN=1,
}
syn.bi = {
    P=1, E=1, VAR=1, SD=1, MAP=1, MPE=1, IDP=1, INFL=1,
    DIST=1, RENAME=1, MUX=1,
    ["ℙ"]=1, ["𝒫"]=1, ["𝔼"]=1, ["𝕍"]=1, ["σ"]=1,
    BERNOULLI=1, RADEMACHER=1, BINOMIAL=1, BETABINOMIAL=1,
    DEGENERATE=1, DUNIF=1, HYPERGEO=1, NEGHYPGEO=1, POIBIN=1,
    FHYPGEO=1, WHYPGEO=1, BENFORD=1, SOLITON=1, RSOLITON=1,
    ZIPF=1, ZIPFM=1,
}
syn.ops = {
    ["="]=1, ["=="]=1, ["≤"]=1, ["<="]=1, ["≥"]=1, [">="]=1,
    ["<"]=1, [">"]=1, ["+"]=1, ["−"]=1, ["-"]=1, ["×"]=1, ["÷"]=1,
    ["/"]=1, ["*"]=1, ["["]=1, ["]"]=1, ["("]=1, [")"]=1,
    [","]=1, [":"]=1, [";"]=1, ["|"]=1, ["↦"]=1, ["&"]=1,
}

-- class ids shared with bayes_editor.h (BAYESL_C_* enum) — the order is
-- the bridge contract.
syn.class_ids = {
    default=0, keyword=1, builtin=2, operator=3, number=4,
    variable=5, enum=6,
}

-- editor text colours in class-id order, pushed to C once via
-- A.bayes_palette ("r,g,b;" per class) — the hues ui_theme.h had
-- compiled in: black/blue/darkblue/grey-dark and the enum green.
syn.editor_palette =
    "30,35,40;0,125,156;0,44,95;104,107,110;104,107,110;" ..
    "30,35,40;24,118,70;"

-- the editor's \cmd → symbol table, pushed once via A.bayes_subs as
-- "cmd=replacement;" pairs (was the static reps[] in bayes_editor.h)
syn.subs_spec =
    "leftrightarrow=↔;rightarrow=→;implies=→;mapsto=↦;times=×;" ..
    "minus=−;land=∧;lnot=¬;nand=↑;lor=∨;neg=¬;nor=↓;iff=↔;xor=⊕;" ..
    "leq=≤;geq=≥;box=□;mcP=𝒫;bbP=ℙ;to=→;le=≤;ge=≥;P=ℙ;"

-- Generic byte-span list for the formula editor: "start,end,class;"
-- per non-default-class token, 0-based byte offsets.  The lexical
-- vocabulary is a parameter so tools other than BayesL (e.g. the
-- regex workspace) reuse the same engine, class ids and palette:
--
--   vocab = {
--     ident(text, i, n)  -> j|nil   identifier scanner ([i,j) bytes)
--     number(text, i, n) -> j|nil   number scanner
--     ops   = {"<->", "<=", ...}    multi-char ops (any order —
--                                 matched longest-first)
--     init() -> ctx                 per-scan classifier state
--     cls(w, kind, ctx) -> class    w = token text, kind one of
--                                 "word" | "number" | "rune" | "op";
--                                 nil/"default" emits nothing
--   }
--
-- Scan order mirrors the original C loop: whitespace, identifier,
-- number, multi-char op, single rune.
function syn.spans_vocab(text, vocab)
    local out, ids = {}, syn.class_ids
    local ctx = vocab.init and vocab.init() or nil
    local ops = vocab.ops
    if ops and #ops > 1 then
        local c = {}
        for i2, op in ipairs(ops) do c[i2] = op end
        table.sort(c, function(a, b) return #a > #b end)
        ops = c
    end
    local i, n = 1, #(text or "")
    while i <= n do
        local b = text:byte(i)
        if b == 32 or b == 9 or b == 10 or b == 13 then
            i = i + 1
        else
            local j, kind
            if vocab.ident then j = vocab.ident(text, i, n) end
            if j then kind = "word"
            elseif vocab.number then
                j = vocab.number(text, i, n)
                if j then kind = "number" end
            end
            if not j and ops then
                for _, op in ipairs(ops) do
                    if text:sub(i, i + #op - 1) == op then
                        j = i + #op; kind = "op"; break
                    end
                end
            end
            if not j then
                j = i + (b < 0x80 and 1 or b < 0xE0 and 2 or
                         b < 0xF0 and 3 or 4)
                kind = "rune"
            end
            local cls = vocab.cls(text:sub(i, j - 1), kind, ctx)
            if cls and cls ~= "default" then
                out[#out + 1] = string.format("%d,%d,%d;",
                                              i - 1, j - 2, ids[cls])
            end
            i = j
        end
    end
    return table.concat(out)
end

-- The BayesL vocabulary on top of the generic engine: identifiers
-- [A-Za-z_][A-Za-z0-9_]*, numbers [0-9][0-9.eE+-]* (the isnumchar
-- quirk keeps "5-3" one token), the multi-char <- >,&&,||,->,<=,>=,==
-- and single runes otherwise; LET/;-bound names are tracked
-- sequentially like the C pass did.
function syn.spans(text, vars, outs)
    return syn.spans_vocab(text, {
        init = function() return {decl = false, bound = {}} end,
        ident = function(t, i, n)
            local b = t:byte(i)
            if not ((b >= 65 and b <= 90) or (b >= 97 and b <= 122)
                    or b == 95) then return nil end
            local j = i + 1
            while j <= n do
                local c = t:byte(j)
                if (c >= 65 and c <= 90) or (c >= 97 and c <= 122)
                   or (c >= 48 and c <= 57) or c == 95 then j = j + 1
                else break end
            end
            return j
        end,
        number = function(t, i, n)
            local b = t:byte(i)
            if not (b >= 48 and b <= 57) then return nil end
            local j = i + 1
            while j <= n and t:sub(j, j):match("[0-9eE+%-.]") do
                j = j + 1
            end
            return j
        end,
        ops = {"<->", "&&", "||", "->", "<=", ">=", "=="},
        cls = function(w, kind, ctx)
            if kind == "word" then
                local c
                if syn.kw[w] then c = "keyword"
                elseif syn.bi[w] then c = "builtin"
                elseif ctx.decl then c = "variable"; ctx.bound[w] = true
                elseif ctx.bound[w] or (vars and vars[w]) then c = "variable"
                elseif outs and outs[w] then c = "enum"
                else c = "default" end
                ctx.decl = (c == "keyword" and w == "LET")
                return c
            elseif kind == "number" then
                ctx.decl = false
                return "number"
            end
            local c
            if w == "<->" or w == "&&" or w == "||" or w == "->" then
                c = "keyword"
            elseif w == "<=" or w == ">=" or w == "==" then
                c = "operator"
            else
                c = syn.kw[w] and "keyword" or syn.bi[w] and "builtin"
                    or syn.ops[w] and "operator" or "default"
            end
            ctx.decl = (w == ";")
            return c
        end,
    })
end

-- class -> {bg, hover, active, fg, border} for A.button_col.  Variables
-- and enum literals get a pale tint so the formula's own names stand
-- out; keywords/builtins/operators keep the standard light face with a
-- coloured label (their symbols are already distinctive).  The active
-- tint stays light because button_col applies one fg to all states.
syn.palette = {
    variable = {bg={233,240,249}, hov={210,224,243}, act={188,210,236},
                fg={30,35,40},    bor={195,212,238}},
    enum     = {bg={229,243,233}, hov={207,236,216}, act={186,229,198},
                fg={24,118,70},   bor={180,214,191}},
    keyword  = {bg={236,244,250}, hov={210,228,242}, act={185,212,232},
                fg={0,125,156},   bor={205,225,240}},
    -- builtins are the query/distribution heads — the heaviest tokens —
    -- so they get a filled navy chip with white text: unmistakable next
    -- to the pale variable/enum/keyword buttons without any font tricks
    builtin  = {bg={0,44,95},     hov={0,72,140},    act={0,96,175},
                fg={255,255,255}, bor={0,44,95}},
    operator = {bg={247,248,248}, hov={220,221,222}, act={205,208,210},
                fg={104,107,110}, bor={220,221,222}},
    number   = {bg={247,248,248}, hov={220,221,222}, act={205,208,210},
                fg={104,107,110}, bor={220,221,222}},
}

-- model identifier vocabularies for highlighting: variable-name set and
-- outcome-name set (identifier-shaped only — anything else can never
-- appear as a formula token).  Used both to classify suggestion buttons
-- and to build the editor's coloured spans.
function syn.name_sets(nodes)
    local vars, outs = {}, {}
    for _, n in ipairs(nodes or {}) do
        local nm = n.name and ffi.string(n.name) or ""
        if nm ~= "" then vars[nm] = true end
        for i = 1, #(n.outc or {}) do
            local o = n.outc[i] and ffi.string(n.outc[i]) or ""
            if o:match("^[A-Za-z_][A-Za-z0-9_]*$") then outs[o] = true end
        end
    end
    return vars, outs
end

-- LET-bound names, by the same lexical rule the C editor applies: the
-- identifier right after "LET" or ";" declares a local (';' is the LET
-- binding separator and occurs nowhere else in the grammar)
function syn.bound_names(text)
    local set = {}
    for nm in (text or ""):gmatch("%f[%a%d_]LET%s+([A-Za-z_][A-Za-z0-9_]*)") do
        set[nm] = true
    end
    for nm in (text or ""):gmatch(";%s*([A-Za-z_][A-Za-z0-9_]*)") do
        set[nm] = true
    end
    return set
end

-- class of a suggestion token (its bare label): "keyword", "builtin",
-- "operator", "number", "variable", "enum" or "default"
function syn.classify(core, vars, bound, outs)
    local base = core
    if #base > 1 and base:sub(-1) == "(" then base = base:sub(1, -2) end
    if syn.kw[base] then return "keyword" end
    if syn.bi[base] then return "builtin" end
    if syn.ops[base] then return "operator" end
    if base:match("^%-?%d") then return "number" end
    if vars and vars[base] then return "variable" end
    if bound and bound[base] then return "variable" end
    if outs and outs[base] then return "enum" end
    return "default"
end


suggest.digit  = digit
suggest.letter = letter
suggest.syn    = syn
return suggest
