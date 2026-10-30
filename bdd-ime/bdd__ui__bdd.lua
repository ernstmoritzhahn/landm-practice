-- ui/bdd.lua -- the BDD editor's frame composition: a bare window
-- whose client area is the graph canvas plus a properties column.
-- The model is G = ui/bdd/state.lua; geometry + interaction come
-- from the shared ui/graphw.lua skeleton.

local ffi   = require "ffi"
local A     = require "ui.api"
local util  = require "ui.util"
local gen   = require "ui.gen"
local G     = require "ui.bdd.state"
local model = require "ui.bdd.model"
local cv    = require "ui.bdd.canvas"
local panel = require "ui.bdd.panel"
local gw    = require "ui.graphw"

local in_rect = util.in_rect
local NK = gen.NK

local f4 = ffi.new("float[4]")
local f2 = ffi.new("float[2]")

local bdd = {}

local BDD_HINTS = {
    {function() return (G.selected or G.sel_edge)
            and "click empty space: close editor"
            or  "click empty space: add node" end, {empty = true}},
    {"drag node: move",                    {ring = true, move = true}},
    {"drag centre: edge",                  {inner = true, connect = true}},
    {"left/right of source = false/true",  {connect = true}},
    {"click node/edge: options",           {ring = true, inner = true,
                                            edge = true}},
    {"Del deletes selection",              {}},
}

local RO_HINTS = {
    {"view only - the diagram cannot be edited", {}},
}

function bdd.frame(x, y, w, h, s, hint)
    G.edit_owned = G.edit_seen
    G.edit_seen = false

    G.NODE_HW   = 20.0 * s
    G.NODE_HH   = 13.0 * s
    G.NODE_C    = 7.0 * s
    G.CONNECT_R = 12.0 * s
    G.DRAG_TH   = 4.0 * s
    G.EDGE_HIT  = 9.0 * s
    G.HOV_HYST  = 4.0 * s
    G.GRID      = 33.0 * s   -- snap quantum (state.lua seeds it too)

    local win_flags = NK.WINDOW_BORDER + NK.WINDOW_BACKGROUND
                      + NK.WINDOW_NO_SCROLLBAR
    if not G.exam then win_flags = win_flags + NK.WINDOW_TITLE end
    if A.begin_titled("BDD", "", x, y, w, h, win_flags) ~= 0 then
        G.win_x, G.win_y, G.win_w, G.win_h = x, y, w, h
        A.content_rect(f4)
        local cw, ch = f4[2], f4[3]
        if cw <= 0 then cw = w - 22 end
        if ch <= 0 then ch = h - 40 end

        local mxx, mxy = -math.huge, -math.huge
        for _, n in ipairs(G.nodes) do
            if n.x > mxx then mxx = n.x end
            if n.y > mxy then mxy = n.y end
        end
        local lm = G.NODE_HH + A.font_height() + 6
        local ext_w, ext_h = 0, 0
        if mxx ~= -math.huge then
            ext_w = mxx + G.NODE_HW + 12
            ext_h = mxy + lm
        end
        G.view_extent = nil
        local HINTS = G.readonly and RO_HINTS or BDD_HINTS
        local hint_n = hint and 1 or #gw.hint_lines(HINTS, s, cw)
        local hint_h = hint_n * (gw.HINT_ROW_H * s + 4)
        local section_h = math.max(20, ch - hint_h - 4)
        local usable = math.max(48, cw - 8 - gw.SPLIT_W)
        G.split_frac = G.split_frac or 0.74
        local cv_px = math.floor(G.split_frac * usable + 0.5)
        cv_px = math.max(120, math.min(usable - 200, cv_px))
        local pm_px = usable - cv_px

        local vflags, est_w, est_h = gw.view_flags(
            ext_w, ext_h, cv_px - 14, section_h - 14, G.cv_scroll)

        A.row_begin(NK.STATIC, section_h, 3)
        A.row_push(cv_px)
        if A.group_begin(G.cv_scroll, "bdd_view", vflags) ~= 0 then
            A.content_rect(f4)
            local vw, vh = f4[2], f4[3]
            if vw <= 0 then vw = est_w end
            if vh <= 0 then vh = est_h end
            cv.widget(math.max(vh, ext_h), math.max(vw, ext_w))
        end
        A.group_end()

        A.row_push(gw.SPLIT_W)
        gw.split_strip(G, usable, G.win_x, 0.3, 0.92)

        A.row_push(pm_px)
        if A.group_begin(G.pm_scroll, "bdd_props",
                         NK.WINDOW_BORDER) ~= 0 then
            A.content_rect(f4)
            G.panel.x, G.panel.y = f4[0], f4[1]
            G.panel.w, G.panel.h = f4[2], f4[3]
            panel.draw()
        end
        A.group_end()
        A.row_end()
        gw.draw_hint(HINTS, G, s, cw, hint)

        if (G.sel_edge or G.selected)
           and not G.edit_owned and not G.readonly
           and (A.key_pressed(NK.KEY_DEL) ~= 0
                or A.key_pressed(NK.KEY_BACKSPACE) ~= 0) then
            if G.sel_edge then model.remove_edge(G, G.sel_edge)
            elseif G.selected then
                model.remove_node(G, G.selected)
            end
        end
    end
    A.end_()

    if (G.selected or G.sel_edge) and G.canvas.w > 0 and G.panel.w > 0
       and A.press_in_rect(G.win_x, G.win_y, G.win_w, G.win_h) ~= 0 then
        A.clicked_pos(f2)
        if not in_rect(f2[0], f2[1], G.canvas)
           and not in_rect(f2[0], f2[1], G.panel) then
            G.selected = nil
            G.sel_edge = nil
        end
    end

    if A.quit_enabled and A.request_quit
       and A.quit_enabled() ~= 0
       and A.key_pressed(NK.KEY_TEXT_RESET_MODE) ~= 0
       and (not A.menu_active or A.menu_active() == 0) then
        A.request_quit()
    end
end

return bdd
