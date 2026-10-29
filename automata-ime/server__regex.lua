-- server/regex.lua — regular expressions in the Sudkamp/course
-- notation: union is ∪, concatenation is juxtaposition, * and + are
-- postfix closures, λ is the empty word, ∅ the empty language;
-- | aliases ∪, · juxtaposes, and a^N expands to N copies.
--
-- the GRAMMAR itself lives in the shared LPeg module
-- ../../teaching/lua/automata/regexp.lua — one implementation for
-- grading and the editor.  This file is the editor-facing adapter:
-- it feeds the shared parser a token list, converts the returned
-- AST (which carries token-index spans) into the UI node shape with
-- source byte spans, and maps its structured failure onto the
-- expected-token protocol the suggestion bar consumes.
--
-- regex.parse(str) -> ast | nil, err
--   ast = {t="sym",s=..} | {t="eps"} | {t="empty"}
--       | {t="union"|"cat", kids={...}} | {t="star"|"plus", kid=..}
--   every node carries byte spans p0/p1 into the source string.
--   err  = {pos=<byte pos>, msg=<string>, exp={<kind>,...}}
--   exp kinds: sym eps empty lp rp union star plus hat digits —
--   the UI maps them onto its insert buttons (BayesL-style
--   expected-token fixes).
--
-- regex.eval(ast, word) -> bool   (Thompson NFA simulation)

local M = {}

-- the shared parser: only the token-level API is needed, so the
-- module installs onto a bare table (no automata.init, no
-- tokenise_word — source anchoring stays ours)
local A = {}
require "automata.regexp"(A)

-- ---------------------------------------------------------------
-- scanner (UTF-8 aware: ∪ λ ∅ are multi-byte) — source anchoring
-- only: it finds the tokens and their byte spans, the shared
-- grammar decides what they mean

local SKIP = {[" "] = true, ["\t"] = true, ["\n"] = true,
              ["\r"] = true,
              ["\xC2\xB7"] = true, ["\xE2\x8B\x85"] = true}  -- · ⋅

-- one UTF-8 char starting at byte i -> char, next index
local function utf8_at(str, i)
    local b = str:byte(i)
    if b < 0x80 then return str:sub(i, i), i + 1 end
    local n = b < 0xE0 and 2 or (b < 0xF0 and 3 or 4)
    return str:sub(i, i + n - 1), i + n
end

local function scan(str)
    local toks, i = {}, 1
    while i <= #str do
        local c, j = utf8_at(str, i)
        if not SKIP[c] then
            toks[#toks + 1] = {s = c, p0 = i, p1 = j - 1}
        end
        i = j
    end
    return toks
end

-- ---------------------------------------------------------------
-- automata AST -> UI node shape: {t,s,kids,kid,p0,p1}.
-- binary choice/sequence chains flatten into the n-ary kids lists
-- the hand parser produced; exponent-expanded sequences drop their
-- synthetic λ head (unspanned — never part of the source)

local function conv(node, toks)
    local ty = node:get_type()
    local p0 = node.t0 and toks[node.t0].p0
    local p1 = node.t1 and toks[node.t1].p1
    if ty == "regexp_primitive" then
        return {t = "sym", s = node.inner, p0 = p0, p1 = p1}
    end
    if ty == "regexp_blank" then
        return {t = "eps", p0 = p0, p1 = p1}
    end
    if ty == "regexp_empty" then
        return {t = "empty", p0 = p0, p1 = p1}
    end
    if ty == "regexp_repetition" then
        return {t = "star", kid = conv(node.inner, toks),
                p0 = p0, p1 = p1}
    end
    if ty == "regexp_plus" then
        return {t = "plus", kid = conv(node.inner, toks),
                p0 = p0, p1 = p1}
    end
    local flat = ty == "regexp_choice" and "regexp_choice"
              or ty == "regexp_sequence" and "regexp_sequence"
    local kids = {}
    local function collect(n)
        if n.get_type and n:get_type() == flat then
            collect(n.left); collect(n.right)
        else
            local k = conv(n, toks)
            if k.t == "eps" and not k.p0 then
                return            -- synthetic λ from a^N expansion
            end
            kids[#kids + 1] = k
        end
    end
    collect(node)
    return {t = ty == "regexp_choice" and "union" or "cat",
            kids = kids, p0 = p0, p1 = p1}
end

-- errtab -> the UI's {pos,msg,exp}: token index -> source byte pos
local OPERAND = {sym = true, lp = true, eps = true, empty = true}

local function to_err(e, toks, str)
    local pos = (e.tokidx and toks[e.tokidx]
                 and toks[e.tokidx].p0) or #str + 1
    local tok = e.tokidx and toks[e.tokidx]
    local msg
    if e.kind == "operand" then
        msg = "expected operand"
    elseif e.kind == "close" then
        msg = e.want == "digits" and "expected a number after '^'"
              or "expected '" .. (e.want or ")") .. "'"
    elseif e.kind == "end" then
        msg = "unexpected '" .. (tok and tok.s or "?") .. "'"
    else
        msg = (e.msg or "syntax error")
              :gsub("^[^:]+:%d+: *", "")
    end
    return {pos = pos, msg = msg, exp = e.exp}
end

-- ---------------------------------------------------------------
-- public interface

function M.parse(str)
    str = str or ""
    local toks = scan(str)
    if #toks == 0 then
        return nil, {pos = 1, msg = "empty expression",
                     exp = OPERAND}
    end
    local tstrs = {}
    for i, t in ipairs(toks) do tstrs[i] = t.s end
    -- course notation: *, +, ^ are operators, never symbols — the
    -- shared grammar would read them as primitives otherwise
    local ast, res = A.parse_regexp_tokens(tstrs, {
        metas = {["*"] = true, ["+"] = true, ["^"] = true}})
    if not ast then
        return nil, to_err(res, toks, str)
    end
    return conv(ast, toks)
end

-- deepest AST node covering byte position p (for caret->tree links)
function M.node_at(ast, p)
    if not ast or not (ast.p0 and p >= ast.p0 and p <= ast.p1) then
        return nil
    end
    local kids = ast.kids or (ast.kid and {ast.kid})
    if kids then
        for _, k in ipairs(kids) do
            local n = M.node_at(k, p)
            if n then return n end
        end
    end
    return ast
end

-- every leaf symbol used (for the alphabet-membership check)
function M.symbols(ast, set)
    set = set or {}
    if not ast then return set end
    if ast.t == "sym" then set[ast.s] = true end
    local kids = ast.kids or (ast.kid and {ast.kid})
    if kids then
        for _, k in ipairs(kids) do M.symbols(k, set) end
    end
    return set
end

-- ---------------------------------------------------------------
-- Thompson NFA construction + simulation for eval

local function build(ast, edges, new)
    if ast.t == "empty" then                 -- no path: rejects all
        return new(), new()
    end
    if ast.t == "eps" or ast.t == "sym" then
        local s, f = new(), new()
        edges[s] = edges[s] or {}
        edges[s][#edges[s] + 1] =
            {ast.t == "eps" and "eps" or ast.s, f}
        return s, f
    end
    if ast.t == "cat" then
        local s, f = new(), new()
        local prev = s
        for _, k in ipairs(ast.kids) do
            local ks, kf = build(k, edges, new)
            edges[prev] = edges[prev] or {}
            edges[prev][#edges[prev] + 1] = {"eps", ks}
            prev = kf
        end
        edges[prev] = edges[prev] or {}
        edges[prev][#edges[prev] + 1] = {"eps", f}
        return s, f
    end
    if ast.t == "union" then
        local s, f = new(), new()
        for _, k in ipairs(ast.kids) do
            local ks, kf = build(k, edges, new)
            edges[s] = edges[s] or {}
            edges[s][#edges[s] + 1] = {"eps", ks}
            edges[kf] = edges[kf] or {}
            edges[kf][#edges[kf] + 1] = {"eps", f}
        end
        return s, f
    end
    -- star / plus: kid looped, plus forces one pass first
    local s, f = new(), new()
    local ks, kf = build(ast.kid, edges, new)
    edges[s] = edges[s] or {}
    edges[s][#edges[s] + 1] = {"eps", ks}
    if ast.t == "star" then
        edges[s][#edges[s] + 1] = {"eps", f}
    end
    edges[kf] = edges[kf] or {}
    edges[kf][#edges[kf] + 1] = {"eps", ks}
    edges[kf][#edges[kf] + 1] = {"eps", f}
    return s, f
end

local function closure(edges, set)
    local queue = {}
    for s in pairs(set) do queue[#queue + 1] = s end
    while #queue > 0 do
        local u = table.remove(queue)
        for _, e in ipairs(edges[u] or {}) do
            if e[1] == "eps" and not set[e[2]] then
                set[e[2]] = true
                queue[#queue + 1] = e[2]
            end
        end
    end
    return set
end

function M.eval(ast, word)
    if not ast then return false end
    local edges, nid = {}, 0
    local function new() nid = nid + 1; return nid end
    local s, f = build(ast, edges, new)
    local cur = closure(edges, {[s] = true})
    local i = 1
    while i <= #word do
        local c
        c, i = utf8_at(word, i)
        local nxt = {}
        for u in pairs(cur) do
            for _, e in ipairs(edges[u] or {}) do
                if e[1] == c then nxt[e[2]] = true end
            end
        end
        cur = closure(edges, nxt)
        if not next(cur) then return false end
    end
    return cur[f] == true
end

return M
