-- ui/aut/re.lua -- the regular-expression workspace (G.mode == "re"),
-- laid out like the BayesL formula column minus the graph: the
-- expression field on top (the same C-side editor widget — insert at
-- caret or at the reported error position, \-substitutions, error
-- underline, status gutter), then the insert-button palette, the
-- expected-token row while the expression does not parse, the syntax
-- tree filling the remaining space, and the test-word row at the
-- bottom.  The expression is the primary object; the tree explains
-- its structure.

local ffi    = require "ffi"
local A      = require "ui.api"
local util   = require "ui.util"
local gen    = require "ui.gen"
local G      = require "ui.aut.state"
local net    = require "ui.aut.net"
local model  = require "ui.aut.model"
local regex  = require "server.regex"
local checks = require "server.checks"
local retree = require "ui.aut.retree"
local gw     = require "ui.graphw"
local syn    = require "ui.suggest".syn
local sugbar = require "ui.sugbar"   -- shared suggestion-bar layout

local NK, NKL = gen.NK, gen.NKL

local re_buf  = ffi.new("char[4096]")
local word_buf = ffi.new("char[256]")
local f4 = ffi.new("float[4]")

local C_RED   = {200, 40, 40}
local C_GREEN = {40, 150, 60}
local C_MUTE  = {120, 124, 128}

local re = {}

-- syntax colouring rides on the SHARED suggestion machinery
-- (ui.suggest / syn): the class ids + palette are the formula
-- editor's, only the lexical vocabulary is regex-specific.  Mapping
-- by grammatical role: alphabet symbols are the "names" (variable),
-- ∪/| the connectives (keyword), λ/∅ literal constants (enum), and
-- */+/()/· punctuation (operator).
local SUBS = "lambda=\xCE\xBB;eps=\xCE\xBB;empty=\xE2\x88\x85;" ..
             "emptyset=\xE2\x88\x85;union=\xE2\x88\xAA;cdot=\xC2\xB7;"
local RE_CLS = {
    ["\xE2\x88\xAA"] = "keyword", ["|"] = "keyword",      -- ∪
    ["*"] = "operator", ["+"] = "operator", ["^"] = "operator",
    ["("] = "operator", [")"] = "operator",
    ["\xC2\xB7"] = "operator",                            -- ·
    ["\xCE\xBB"] = "enum", ["\xE2\x88\x85"] = "enum",     -- λ ∅
}
local RE_VOCAB = {
    cls = function(w) return RE_CLS[w] or "variable" end,
}
local inited = false

local re_last = nil     -- expression text the editor field holds
local word_for = nil    -- test-word text the buffer mirrors
local dump_done = false -- AUT_NODES one-shot
local dbg_snap = nil    -- AUT_DBG_RE change detector

-- cached parse of the current expression (rebuilt on change only;
-- the tree + expected row + status all read it)
local P = {src = nil, ast = nil, err = nil}
local function parsed()
    local s = G.regex or ""
    if P.src ~= s then
        P.src = s
        P.ast, P.err = regex.parse(s)
    end
    return P.ast, P.err
end

-- insert a literal at the text caret (bayes_splice splices bytes at
-- a 1-based range; bayes_insert would append at the end/the error
-- position — expected-token buttons want that, the palette wants
-- plain caret insertion)
local function insert_at_caret(tok)
    local cb = A.bayes_cursor_byte and A.bayes_cursor_byte() or -1
    if A.bayes_splice and cb >= 0 then
        A.bayes_splice(cb + 1, cb + 1, tok, #tok)
    else
        A.bayes_insert(tok, #tok)
    end
    A.bayes_focus()
end



local function char_len(b)
    return b < 0x80 and 1 or (b < 0xE0 and 2 or (b < 0xF0 and 3 or 4))
end

-- char at 1-based byte pos -> {start, past-end} byte span
-- (continuation bytes belong to the glyph before them)
local function char_span(s, p)
    while p > 1 do
        local c = s:byte(p) or 0
        if c >= 0x80 and c < 0xC0 then p = p - 1 else break end
    end
    return p, p + char_len(s:byte(p) or 0)
end

-- delete the char ending at the caret (the red "←" of the formula
-- editor: DEL_TOK); at caret 0 there is nothing to delete
local function del_before_caret()
    local cb = A.bayes_cursor_byte and A.bayes_cursor_byte() or 0
    if cb <= 0 then A.bayes_focus() return end
    local from = char_span(G.regex or "", cb)
    A.bayes_splice(from, cb + 1, "", 0)
    A.bayes_focus()
end

local UNI = {union = "\xE2\x88\xAA", star = "*", plus = "+",
             hat = "^",
             lp = "(", rp = ")",
             eps = "\xCE\xBB", empty = "\xE2\x88\x85"}

-- the suggestion bar — BayesL semantics: it follows the CARET, not
-- the error.  The expected tokens are computed from the expression
-- prefix left of the caret: a parseable prefix offers the legal
-- continuations (a symbol concatenates, ∪/*/+ extend), an
-- incomplete prefix the tokens it still misses (operand starts, a
-- closing ')' inside an open group, ...).  A mid-text error can
-- only be fixed by deleting the offending char, so that deletion is
-- offered next to it.  Token clicks splice at the caret — like the
-- formula editor's ins_from/ins_to, where the range is the caret.
-- continuations of a complete expression: any operand starts a
-- concatenation (symbol, '(' group, λ, ∅), ∪ opens an alternative,
-- */+ close over — only ')' is impossible (an open group's ')' is
-- suggested by the incomplete-prefix branch instead)
local CONT = {sym = true, lp = true, eps = true, empty = true,
              union = true, star = true, plus = true, hat = true}
local SUG_ORDER = {"sym", "lp", "eps", "empty",
                   "union", "star", "plus", "hat", "rp"}

local function suggest_bar(err, syms, h, cb, w, s)
    local items = {}
    if #(G.regex or "") > 0 then
        items[#items + 1] = {del_caret = true, label = sugbar.DEL}
    end
    if err and err.pos <= #(G.regex or "") then
        local p0, p1 = char_span(G.regex, err.pos)
        items[#items + 1] = {label = "delete '" ..
                                 G.regex:sub(p0, p1 - 1) .. "'",
                             del = p0, delto = p1}
    end
    -- expected tokens at the caret: parse the prefix up to it.
    -- A valid prefix takes the plain continuation set; an
    -- incompletely-ending prefix its own expected set; a prefix
    -- already broken mid-text offers nothing.
    local prefix = (G.regex or ""):sub(1, math.max(0, cb))
    local past, perr = regex.parse(prefix)
    local exp
    if past then
        exp = CONT
    elseif perr and perr.pos > #prefix then
        exp = perr.exp
    end
    if exp then
        if exp.sym then
            for _, s in ipairs(syms or {}) do
                items[#items + 1] = {label = s, tok = s,
                                     cls = "variable"}
            end
        end
        for _, k in ipairs(SUG_ORDER) do
            if k ~= "sym" and exp[k] then
                items[#items + 1] = {label = UNI[k], tok = UNI[k],
                                     cls = RE_CLS[UNI[k]]}
            end
        end
    end
    if #items == 0 then return 0 end
    -- shared layout: measured-width packing against the pane width
    -- (~15 % overshoot like the formula bar), proportional emission
    local cap = math.max(60, w - 8 * s) * 1.15
    local rows = sugbar.pack(items, cap)
    for _, row in ipairs(rows) do
        sugbar.emit_row(row, {
            w_px = w, h = h,
            on_click = function(it)
                if G.readonly then return end
                if it.del_caret then
                    del_before_caret()
                elseif it.del then
                    A.bayes_splice(it.del, it.delto, "", 0)
                    A.bayes_focus()
                else
                    insert_at_caret(it.tok)
                end
            end,
        })
    end
    return #rows * (h + 6)
end

-- the workspace, emitted inside the left column's group; `w`,`h` is
-- the column's content size
function re.draw(w, h, s)
    local ast, err = parsed()

    -- nuklear adds ~4px row spacing after every emitted row; the
    -- height budget below must account for it or the bottom test row
    -- falls under the (scrollbar-less) outer group's clip edge
    local GAP = 6

    -- one-time editor setup: the shared class palette, the
    -- regex-specific \-substitutions
    if not inited then
        inited = true
        if A.bayes_palette then
            A.bayes_palette(syn.editor_palette, #syn.editor_palette)
        end
        if A.bayes_subs then A.bayes_subs(SUBS, #SUBS) end
        re_last = nil
    end

    -------------------------------------------------- editor row
    local fstate = NKL.BAYES_NONE
    if (G.regex or "") ~= "" then
        fstate = ast and NKL.BAYES_VALID or NKL.BAYES_INVALID
    end
    A.bayes_status(fstate)
    local ed_h = math.floor(28 * s + 0.5)
    A.bayes_height(ed_h)
    -- the error span doubles as the INSERT position for suggestion
    -- clicks (bayes_insert splices at err_from-1): a trailing error
    -- must point past the text end so inserts append; an on-char
    -- error underlines the whole glyph (walk back to its lead byte)
    if err then
        local p = err.pos
        if p <= #(G.regex or "") then
            p = char_span(G.regex, p)
            A.bayes_error(p, p + char_len(G.regex:byte(p) or 0))
        else
            A.bayes_error(p, p + 1)      -- at end: inserts append
        end
    else
        A.bayes_error(0, 0)
    end
    if A.bayes_spans then
        local sp = syn.spans_vocab(G.regex or "", RE_VOCAB)
        A.bayes_spans(sp, #sp)
    end
    A.bayes()
    if A.bayes_active() ~= 0 then G.edit_seen = true end
    -- like the formula editor's field: text cursor on hover, and an
    -- invalid expression pops the parse message as a tooltip (emitted
    -- at window level by ui.aut — inside the group the popup would
    -- anchor to the layout clip)
    local f_hov = A.bayes_hovered and A.bayes_hovered() ~= 0
    if f_hov and A.set_cursor then
        A.set_cursor(NKL.CURSOR_TEXT, 0)
    end
    re.tip = (err and f_hov) and (err.msg or "syntax error") or nil

    -- caret -> tree highlight: deepest node covering the byte right
    -- of the caret (fall back to the byte left of it)
    local active
    if ast and A.bayes_cursor_byte then
        local cb = A.bayes_cursor_byte()
        if cb and cb >= 0 then
            active = regex.node_at(ast, math.min(cb + 1, #G.regex))
                   or regex.node_at(ast, cb)
        end
    end
    if active and A.bayes_active_range then
        A.bayes_active_range(active.p0, active.p1 + 1)
    else
        A.bayes_active_range(0, 0)
    end

    -- the pointer's byte position shares the caret's deepest-node
    -- lookup (the formula editor's resolve_xhl order: formula hover
    -- first, tree hover below only fills in when it reports none)
    local txt_hov
    if ast and A.bayes_hover_pos and (G.regex or "") ~= "" then
        local hp = A.bayes_hover_pos()
        if hp > 0 then
            txt_hov = regex.node_at(ast, math.min(hp, #(G.regex or "")))
        end
    end

    -- field <-> state sync, both directions: the first sync pushes
    -- the model (AUT_RE seed / model load before the editor existed);
    -- after that the C side's change edge decides — an edit pulls
    -- into G.regex, an external write (model.load, reset) pushes back
    if re_last == nil and (G.regex or "") ~= "" then
        A.bayes_set(G.regex, #G.regex)
    end
    local changed = A.bayes_changed() ~= 0
    local n = A.bayes_text(re_buf, 4096)
    local txt = ffi.string(re_buf, n)
    re_last = txt
    -- AUT_DBG_RE (dev): trace buffer/selection/caret whenever they move
    if os.getenv and os.getenv("AUT_DBG_RE") and A.bayes_sel_start then
        local s0, s1 = A.bayes_sel_start(), A.bayes_sel_end()
        local cur = A.bayes_cursor_byte and A.bayes_cursor_byte() or -1
        local snap = txt .. "|" .. s0 .. "," .. s1 .. "|" .. cur
        if snap ~= dbg_snap then
            dbg_snap = snap
            io.stderr:write(("re: txt=%q sel=%d..%d cb=%d chg=%d\n")
                            :format(txt, s0, s1, cur, changed and 1 or 0))
        end
    end
    if txt ~= (G.regex or "") then
        if changed then
            G.regex = txt
            -- model.on_changed is the answer-changed hook (ui.lua
            -- wraps it to count student edits for sendDataToExternal;
            -- net.dirty alone would skip that)
            if model.on_changed then model.on_changed() else net.dirty() end
        else
            A.bayes_set(G.regex or "", #(G.regex or ""))
        end
    end

    -------------------------------------------------- palette
    local alist = checks.parse_alphabet(G.alphabet)
    local bh = math.floor(24 * s + 0.5)
    local used = ed_h + GAP

    -------------------------------------------------- suggestion bar
    -- no permanent palette — like the formula editor, the bar is
    -- computed per caret position and shows exactly what may be
    -- inserted there (or what fixes the parse error)
    local cb = A.bayes_cursor_byte and A.bayes_cursor_byte()
               or #(G.regex or "")
    used = used + suggest_bar(err, alist, bh, cb, w, s)

    -------------------------------------------------- tree group
    local test_h = math.floor(30 * s + 0.5) + 4
    -- extra slack for the group's border/padding: a few dead pixels
    -- under the tree are invisible, a clipped test row is not
    local tree_h = math.max(40, h - used - test_h - GAP - 12)
    local tw = w - 4
    local ext_w, ext_h = 0, 0
    if ast then
        local r  = retree.R  * s
        local dx = retree.DX * s
        local dy = retree.DY * s
        -- preflight the extent for the group's scrollbars (the draw
        -- below runs the same layout pass)
        local _, exw, exh = retree.layout(ast, dx, dy, r)
        ext_w, ext_h = exw, exh
    end
    local vf, ew2, eh2 = gw.view_flags(ext_w, ext_h, tw, tree_h - 2,
                                     G.re_scroll)
    A.row(tree_h, 1)
    if A.group_begin(G.re_scroll, "re_tree", vf) ~= 0 then
        A.content_rect(f4)
        local vw, vh = f4[2], f4[3]
        if vw <= 0 then vw = ew2 end
        if vh <= 0 then vh = eh2 end
        if ast then
            retree.draw(ast, active, vw, vh, s)
            -- AUT_NODES=1 (dev): dump node centres once for scripted
            -- fake_click reproductions
            if os.getenv and os.getenv("AUT_NODES") and not dump_done then
                dump_done = true
                for nd, p in pairs(retree.last.pos) do
                    io.stderr:write(("node %s @ %.0f,%.0f\n"):format(
                        nd.t, retree.last.ox + p.x, retree.last.oy + p.y))
                end
            end
            -- the formula's hover wins over the tree's — resolve_xhl
            -- order; the light mark follows the pointer while
            -- active_range stays pinned to the caret's node
            local hov_nd = txt_hov or retree.hovered
            if A.bayes_highlight then
                if hov_nd then
                    A.bayes_highlight(hov_nd.p0, hov_nd.p1 + 1)
                else
                    A.bayes_highlight(0, 0)
                end
            end
            if retree.hovered and A.set_cursor then
                A.set_cursor(NKL.CURSOR_HAND, 0)
            end
            if retree.clicked then
                local nd = retree.clicked
                A.bayes_select(nd.p0, nd.p1 + 1)
                A.bayes_focus()
            end
        else
            A.row(20, 1)
            A.text_color(util.pk(C_MUTE))
            A.label((G.regex or "") == ""
                    and "the syntax tree appears here"
                    or  "not a valid expression",
                    NK.TEXT_LEFT)
            A.text_color(util.pk(gen.THEME.BLACK))
            if A.bayes_highlight then A.bayes_highlight(0, 0) end
        end
        A.group_end()
    end

    -------------------------------------------------- test word
    if word_for ~= G.re_word then
        word_for = G.re_word or ""
        util.set_str(word_buf, word_for)
    end
    A.row_begin(NK.STATIC, test_h - 4, 3)
    A.row_push(74)
    A.label("Test word:", NK.TEXT_LEFT)
    A.row_push(math.max(60, w * 0.28))
    local ev = A.edit_zt(NK.EDIT_FIELD |
                         (G.readonly and NK.EDIT_READ_ONLY or 0),
                         word_buf, 255)
    if util.hasflag(ev, NK.EDIT_ACTIVE) then G.edit_seen = true end
    local wd = ffi.string(word_buf)
    -- \lambda completes to λ like in the label field; inside a word λ
    -- is a zero-width concat operand — "aλb" is "ab", "λλ" is the
    -- empty word (an explicit empty-word test, distinct from an
    -- empty field which stays "no input")
    local wcur = A.edit_cursor and A.edit_cursor() or -1
    local cv, wnc = util.sub_track_cursor(wd, wcur, "\\lambda", "\xCE\xBB")
    cv, wnc = util.sub_track_cursor(cv, wnc, "\\lamda", "\xCE\xBB")
    cv, wnc = util.sub_track_cursor(cv, wnc, "\\eps", "\xCE\xBB")
    if cv ~= wd then
        util.set_str(word_buf, cv); wd = cv
        if A.edit_set_cursor and wnc >= 0 then A.edit_set_cursor(wnc) end
    end
    if wd ~= (G.re_word or "") then G.re_word = wd end
    A.row_push(math.max(40, w - 74 - w * 0.28 - 16))
    if ast and wd ~= "" then
        local ok = regex.eval(ast, (wd:gsub("\xCE\xBB", "")))
        A.text_color(util.pk(ok and C_GREEN or C_RED))
        A.label(ok and "accepts" or "rejects", NK.TEXT_LEFT)
        A.text_color(util.pk(gen.THEME.BLACK))
    elseif ast then
        -- an empty field is a missing input, not the empty word —
        -- name it so, no verdict either way
        A.text_color(util.pk(C_MUTE))
        A.label("(no input)", NK.TEXT_LEFT)
        A.text_color(util.pk(gen.THEME.BLACK))
    else
        A.label("", NK.TEXT_LEFT)
    end
    A.row_end()
end

return re
