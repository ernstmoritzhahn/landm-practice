-- ui/aut.lua -- the automaton editor's frame composition: a bare
-- window whose whole client area is the graph canvas.  No server, no
-- formula row — this is the drawing/editing widget only (panels,
-- alphabet editing and exports come later).  The model is G =
-- ui/aut/state.lua; geometry + interaction come from the shared
-- ui/graphw.lua skeleton.

local ffi   = require "ffi"
local A     = require "ui.api"
local util  = require "ui.util"
local gen   = require "ui.gen"
local G     = require "ui.aut.state"
local model = require "ui.aut.model"
local cv    = require "ui.aut.canvas"
local panel = require "ui.aut.panel"
local re    = require "ui.aut.re"
local gw    = require "ui.graphw"

local in_rect = util.in_rect
local NK, NKL = gen.NK, gen.NKL

local f4 = ffi.new("float[4]")
local f2 = ffi.new("float[2]")

local aut = {}

-- bottom hint bar: "|"-separated gesture help, the segment matching
-- G.hover_ctx highlighted (drawn by the shared graphw machinery)
local AUT_HINTS = {
    {function() return (G.selected or G.sel_edge)
            and "click empty space: close editor"
            or  "click empty space: add state" end, {empty = true}},
    {"drag state: move",              {ring = true, move = true}},
    {"drag centre: transition",       {inner = true, connect = true}},
    {"drop on same state: loop",      {connect = true}},
    {"click state/arrow: options",    {ring = true, inner = true,
                                       edge = true}},
    {"Del deletes selection",         {}},
}

-- read-only views (given diagrams, review mode): no gesture help —
-- a single note instead of editing instructions
local RO_HINTS = {
    {"view only - the diagram cannot be edited", {}},
}

-- re mode: no gestures to highlight, plain usage hints
local RE_HINTS = {
    {"buttons insert at the caret",    {}},
    {"\xE2\x8C\xAB deletes char before the caret", {}},
    {"\\lambda types \xCE\xBB",        {}},
    {"click tree node: selects span",  {}},
    {"invalid: a fix button appears",  {}},
}

function aut.frame(x, y, w, h, s, hint)
    -- edit widgets report ACTIVE only while being emitted (in
    -- panel.draw, after the Del check below): the guard therefore
    -- reads the PREVIOUS frame's flag, reset here each frame
    G.edit_owned = G.edit_seen
    G.edit_seen = false

    -- rescale the interaction constants like ui_frame does for E
    G.NODE_R    = 22.0 * s
    G.NODE_C    = 7.0 * s
    G.CONNECT_R = 12.0 * s
    G.DRAG_TH   = 4.0 * s
    G.EDGE_HIT  = 9.0 * s
    G.HOV_HYST  = 4.0 * s
    G.GRID      = 66.0 * s   -- invisible placement grid (3 node radii)

    -- exam mode skips the window title bar — it only eats ~30px of
    -- the question's vertical space there
    local win_flags = NK.WINDOW_BORDER + NK.WINDOW_BACKGROUND
                      + NK.WINDOW_NO_SCROLLBAR
    if not G.exam then win_flags = win_flags + NK.WINDOW_TITLE end
    if A.begin_titled("Automaton", "", x, y, w, h, win_flags) ~= 0 then
        G.win_x, G.win_y, G.win_w, G.win_h = x, y, w, h
        A.content_rect(f4)
        local cw, ch = f4[2], f4[3]
        if cw <= 0 then cw = w - 22 end
        if ch <= 0 then ch = h - 40 end

        -- content extent (rightmost/bottommost state + margin) sizes
        -- the scrollable widget.  Positions stay ABSOLUTE: no
        -- view_extent normalisation, or dragging the leftmost state
        -- would visibly shift all the others.
        local mxx, mxy = -math.huge, -math.huge
        for _, n in ipairs(G.nodes) do
            if n.x > mxx then mxx = n.x end
            if n.y > mxy then mxy = n.y end
        end
        local lm = G.NODE_R + A.font_height() + 6
        local ext_w, ext_h = 0, 0
        if mxx ~= -math.huge then
            ext_w = mxx + G.NODE_R + 12
            ext_h = mxy + lm
        end
        G.view_extent = nil
        -- the mode selects the workspace: automaton canvas vs the
        -- regular-expression editor (formula-column layout)
        local is_re = (G.mode == "re")
        local HINTS = G.readonly and RO_HINTS
                      or (is_re and RE_HINTS or AUT_HINTS)
        -- Resizable columns like the BayesL frame: canvas | grab strip
        -- | properties.  G.split_frac is the canvas share of the
        -- non-splitter width; STATIC pushes because the strip is a
        -- fixed pixel width.
        local hint_n = hint and 1
                       or #gw.hint_lines(HINTS, s, cw)
        local hint_h = hint_n * (gw.HINT_ROW_H * s + 4)
        local section_h = math.max(20, ch - hint_h - 4)
        -- usable width loses the splitter AND the row's item spacing
        -- ((cols-1)*4px) — forgetting the spacing pushes the last
        -- column 8px past the window edge (clipped button borders)
        local usable = math.max(48, cw - 8 - gw.SPLIT_W)
        G.split_frac = G.split_frac or 0.74
        local cv_px = math.floor(G.split_frac * usable + 0.5)
        cv_px = math.max(120, math.min(usable - 200, cv_px))
        local pm_px = usable - cv_px

        -- canvas scrollbars: decided per axis against the canvas column
        local vflags, est_w, est_h = gw.view_flags(
            ext_w, ext_h, cv_px - 14, section_h - 14, G.cv_scroll)

        A.row_begin(NK.STATIC, section_h, 3)
        A.row_push(cv_px)
        if is_re then
            -- the re workspace is a fixed column of controls; only
            -- the syntax tree inside scrolls, so the outer group
            -- keeps its scrollbars off
            if A.group_begin(G.cv_scroll, "re_view",
                             NK.WINDOW_NO_SCROLLBAR) ~= 0 then
                A.content_rect(f4)
                local vw, vh = f4[2], f4[3]
                if vw <= 0 then vw = cv_px - 14 end
                if vh <= 0 then vh = section_h - 14 end
                re.draw(vw, vh, s)
            end
            A.group_end()
            -- parse-error tooltip for the expression row, emitted at
            -- window level like the formula editor's (inside the
            -- group the popup would anchor to the layout clip)
            if re.tip and A.tooltip_begin then
                local msg = re.tip
                local tw = math.min(A.text_width(msg, -1) + 24, 340)
                if A.tooltip_begin(tw) ~= 0 then
                    local fh = A.font_height()
                    for ln in util.wrap_text(msg, tw - 16)
                              :gmatch("[^\n]+") do
                        A.row(fh + 4, 1)
                        A.label(ln, NK.TEXT_LEFT)
                    end
                    A.tooltip_end()
                end
            end
        elseif A.group_begin(G.cv_scroll, "aut_view", vflags) ~= 0 then
            A.content_rect(f4)
            local vw, vh = f4[2], f4[3]
            if vw <= 0 then vw = est_w end
            if vh <= 0 then vh = est_h end
            cv.widget(math.max(vh, ext_h), math.max(vw, ext_w))
        end
        A.group_end()

        -- shared column splitter (graphw): drag the strip to rebalance
        A.row_push(gw.SPLIT_W)
        gw.split_strip(G, usable, G.win_x, 0.3, 0.92)

        -- properties column: the panel emits plain rows; its rect also
        -- serves the skeleton's inside_panel guard
        A.row_push(pm_px)
        if A.group_begin(G.pm_scroll, "aut_props",
                         NK.WINDOW_BORDER) ~= 0 then
            A.content_rect(f4)
            G.panel.x, G.panel.y = f4[0], f4[1]
            G.panel.w, G.panel.h = f4[2], f4[3]
            panel.draw()
        end
        A.group_end()
        A.row_end()
        gw.draw_hint(HINTS, G, s, cw, hint)

        -- Del/Backspace deletes the selection (transition first) —
        -- unless a panel edit field owned last frame's keyboard
        -- input; in re mode the expression field owns the keys
        if not is_re and (G.sel_edge or G.selected)
           and not G.edit_owned and not G.readonly
           and (A.key_pressed(NK.KEY_DEL) ~= 0
                or A.key_pressed(NK.KEY_BACKSPACE) ~= 0) then
            if G.sel_edge then model.remove_edge(G, G.sel_edge)
            elseif G.selected then model.remove_state(G, G.selected) end
        end
    end
    A.end_()

    -- a click outside the canvas and outside the properties column
    -- closes the state/transition editor
    if (G.selected or G.sel_edge) and G.canvas.w > 0 and G.panel.w > 0
       and A.press_in_rect(G.win_x, G.win_y, G.win_w, G.win_h) ~= 0 then
        A.clicked_pos(f2)
        if not in_rect(f2[0], f2[1], G.canvas)
           and not in_rect(f2[0], f2[1], G.panel) then
            G.selected = nil
            G.sel_edge = nil
        end
    end

    -- ESC quits (same convention as the BN frame: nothing consumes it
    -- here, so the first press always quits)
    if A.quit_enabled and A.request_quit
       and A.quit_enabled() ~= 0
       and A.key_pressed(NK.KEY_TEXT_RESET_MODE) ~= 0
       and (not A.menu_active or A.menu_active() == 0) then
        A.request_quit()
    end
end

return aut
