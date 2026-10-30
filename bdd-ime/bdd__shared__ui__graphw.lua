-- ui/graphw.lua -- shared interactive graph-canvas skeleton: widget &
-- clip bookkeeping, the anchor/view-offset maths, the cached hover
-- scan (node + edge hysteresis), the press/drag/connect gesture, the
-- contextual cursor and the scissor wrap.  Extracted verbatim in
-- behaviour from ui/canvas.lua's graph_widget so other node+edge
-- tools reuse the same interaction machinery.
--
-- The skeleton reads/writes these G fields (the tool's state table —
-- for BN this is ui/state.lua's E):
--   nodes, edges, nodes_ver, canvas {x,y,w,h,vx,vy,vw,vh,ox,oy},
--   panel {x,y,w,h}, anchor_x/y, view_extent {lx,ly,...},
--   hovered, hov_edge, hov_edge_prev, hover_ctx, hover_key,
--   press_x/y, dragging, drag_dx/dy, drag_moved, connecting,
--   selected, sel_edge, label_epoch,
--   NODE_R, CONNECT_R, EDGE_HIT, HOV_HYST, DRAG_TH
--
-- Everything semantic is delegated to `ops`:
--   ops.hit_node(mx, my) -> index|nil        -- SCREEN coords
--   ops.hit_edge(mx, my, halfw) -> index|nil -- halfw: EDGE_HIT(+hyst)
--   ops.hit_edge_i(i, mx, my, halfw) -> bool -- single-edge retest
--   ops.add_node(G, x, y)                    -- MODEL coords
--   ops.add_edge(G, from_id, to_id)
--   ops.self_loop = true  -- drop on the source adds a self-edge
--   ops.moved(G, i)       -- optional: a node finished a real drag —
--                         positions persist only if the app counts it
--                         -- (otherwise release-on-source selects it)
--   ops.snap(x, y, node_id) -> x, y  -- model-space snap (grid);
--                         -- applied to drags (node_id is the dragged
--                         -- node, may be nil); the tool applies it in
--                         -- add_node too
--   ops.after_hover(G)    -- per-frame hook (BN mirrors bn_hovered)
--   ops.draw(canvas, ctx) -- the whole scene, incl. connect preview;
--                         -- gw.connect_preview(canvas, ctx) draws the
--                         -- default straight blue ray when ctx.connect_from
--                         -- is set
--   ops.cursor(ctx_str, G) -> id, prio   -- pointer-shape override
--   ops.readonly() -> bool               -- review mode: hover/select
--                                        -- stays, mutations skipped
--
-- ctx passed to draw: {G, bx,by,bw,bh, vox,voy, vx0..vy1, mx,my, fh,
--                      label_margin, over_panel, over_menu, in_view,
--                      ox,oy,ow,oh (pre-scissor clip), connect_from}

local ffi   = require "ffi"
local A     = require "ui.api"
local util  = require "ui.util"
local gen   = require "ui.gen"

local in_rect = util.in_rect
local clamp = util.clamp
local col, pk = util.col, util.pk
local TH, NK, NKL = gen.THEME, gen.NK, gen.NKL

local f4    = ffi.new("float[4]")
local f2    = ffi.new("float[2]")
local clip4 = ffi.new("float[4]")

local gw = {}

-- ---------------------------------------------------------------------
-- context hint bar (optional): a bottom strip of "|"-separated help
-- segments.  Each segment is {text-or-function, {ctx=true, ...}}; the
-- segment whose context key matches G.hover_ctx is drawn highlighted —
-- no bold font is baked, so the active segment is drawn twice with a
-- 1px offset.  The segment list lives with the tool.

gw.HINT_ROW_H = 22
local HINT_SEP    = " | "
local HINT_HL     = {207, 227, 241}   -- pale navy: active segment
local H_CLEAR     = pk({0, 0, 0, 0})

local function hint_text(seg)
    local t = seg[1]
    if type(t) == "function" then t = t() end
    return tostring(t or "")
end

-- wrap segments into lines fitting group_w; each line is a list of
-- segment indices.  Returns the line list — its length is the row count
-- the caller must reserve BEFORE emitting the canvas row.
function gw.hint_lines(segs, s, group_w)
    local row_w = math.max(80, group_w - 4)
    local avail = row_w - 4
    local sepw = A.text_width(HINT_SEP, -1)
    local lines = {{}}
    local lx = 0
    for i = 1, #segs do
        local tw2 = A.text_width(hint_text(segs[i]), -1)
        local need = tw2 + (lx > 0 and sepw or 0)
        if lx > 0 and lx + need > avail then
            lines[#lines + 1] = {}
            lx = 0
            need = tw2
        end
        lines[#lines][#lines[#lines] + 1] = i
        lx = lx + need
    end
    return lines
end

-- emit the hint rows (call after the canvas group).  `hint` overrides
-- the segments with a single plain line (the C-side one-line help).
function gw.draw_hint(segs, G, s, group_w, hint)
    if not group_w or group_w <= 0 then group_w = 400 * s end
    if hint then
        A.row(gw.HINT_ROW_H * s, 1)
        if A.widget(f4) ~= 0 then
            local hc = A.canvas()
            local hfh = A.font_height()
            A.draw_text(hc, f4[0] + 2,
                        f4[1] + (f4[3] - hfh) * 0.5,
                        f4[2] - 4, hfh,
                        tostring(hint), -1, H_CLEAR, pk(TH.BLACK))
        end
        return 1
    end
    local lines = gw.hint_lines(segs, s, group_w)
    local sepw = A.text_width(HINT_SEP, -1)
    for li = 1, #lines do
        A.row(gw.HINT_ROW_H * s, 1)
        if A.widget(f4) ~= 0 then
            local hc = A.canvas()
            local hfh = A.font_height()
            local hfy = f4[1] + (f4[3] - hfh) * 0.5
            local hfx = f4[0] + 2
            local line = lines[li]
            for k = 1, #line do
                local seg = segs[line[k]]
                if k > 1 then
                    A.draw_text(hc, hfx, hfy, sepw + 1, hfh,
                                HINT_SEP, -1, H_CLEAR, pk(TH.BLACK))
                    hfx = hfx + sepw
                end
                local stxt = hint_text(seg)
                local tw2 = A.text_width(stxt, -1)
                if seg[2] and seg[2][G.hover_ctx] then
                    A.fill_rect(hc, hfx - 1, f4[1] + 1, tw2 + 3,
                                f4[3] - 2, 3.0, col(HINT_HL))
                    A.draw_text(hc, hfx, hfy, tw2 + 1, hfh, stxt, -1,
                                H_CLEAR, pk(TH.DARKBLUE))
                    A.draw_text(hc, hfx + 1.0, hfy, tw2 + 1, hfh,
                                stxt, -1, H_CLEAR, pk(TH.DARKBLUE))
                else
                    A.draw_text(hc, hfx, hfy, tw2 + 1, hfh, stxt, -1,
                                H_CLEAR, pk(TH.BLACK))
                end
                hfx = hfx + tw2
            end
        end
    end
    return #lines
end

-- default connect-preview: the straight blue ray BN always used
function gw.connect_preview(canvas, ctx)
    local f = ctx.connect_from
    if f and ctx.mx then
        A.stroke_line(canvas, f.x, f.y, ctx.mx, ctx.my, 2.0,
                      col(TH.BLUE))
    end
end

-- default cursor map: connect in progress or the node centre is a
-- crosshair; a movable ring (or a drag in progress) is the move
-- arrows; a clickable edge gets the hand.  Gestures pick at prio 1.
local function default_cursor(ctx, G)
    if G.connecting or ctx == "inner" then
        return NKL.CURSOR_CROSSHAIR, G.connecting and 1 or 0
    elseif G.dragging or ctx == "ring" then
        return NKL.CURSOR_MOVE, G.dragging and 1 or 0
    elseif ctx == "edge" then
        return NKL.CURSOR_HAND, 0
    end
end
gw.default_cursor = default_cursor

function gw.widget(height, width, G, ops)
    local cb = G.canvas
    if width then
        A.row_begin(NK.STATIC, height, 1)
        A.row_push(width)
    else
        A.row(height, 1)
    end
    local st = A.widget(f4)
    if width then A.row_end() end
    if st == NK.WIDGET_INVALID then return end
    local canvas = A.canvas()
    local bx, by = f4[0], f4[1]
    local bw, bh = f4[2], f4[3]
    cb.x, cb.y, cb.w, cb.h = bx, by, bw, bh

    -- the group clip ∩ the widget is the visible viewport
    A.get_clip(canvas, clip4)
    local ox, oy, ow, oh = clip4[0], clip4[1], clip4[2], clip4[3]
    local vx0 = math.max(ox, bx)
    local vy0 = math.max(oy, by)
    local vx1 = math.min(ox + ow, bx + bw)
    local vy1 = math.min(oy + oh, by + bh)
    cb.vx, cb.vy = vx0, vy0
    cb.vw, cb.vh = math.max(0, vx1 - vx0), math.max(0, vy1 - vy0)

    A.mouse_pos(f2)
    local mx, my = f2[0], f2[1]
    local fh = A.font_height()
    local label_margin = G.NODE_R + fh + 6

    -- model->canvas view offset (anchor or overflow margin)
    local vox, voy = 0, 0
    if G.anchor_x then
        if bw > cb.vw + 0.5 then
            vox = math.floor(G.NODE_R + 6
                             - (G.view_extent and G.view_extent.lx or 0)
                             + 0.5)
        else
            vox = math.floor(bw * 0.5 - G.anchor_x + 0.5)
        end
        if bh > cb.vh + 0.5 then
            voy = math.floor(label_margin
                             - (G.view_extent and G.view_extent.ly or 0)
                             + 0.5)
        else
            voy = math.floor(bh * 0.5 - G.anchor_y + 0.5)
        end
    elseif G.view_extent then
        if bw > cb.vw + 0.5 then
            vox = math.floor(G.NODE_R + 6 - G.view_extent.lx + 0.5)
        end
        if bh > cb.vh + 0.5 then
            voy = math.floor(label_margin - G.view_extent.ly + 0.5)
        end
    end
    cb.ox, cb.oy = vox, voy

    local in_view = mx >= vx0 and mx < vx1 and my >= vy0 and my < vy1
    local over_menu = A.menu_active and A.menu_active() ~= 0
    local over_panel = (G.selected or G.sel_edge)
                       and in_rect(mx, my, G.panel)

    -- cached hover scan (see ui/canvas.lua for the key rationale)
    local hkey = table.concat({mx, my, cb.x or 0, cb.y or 0,
        vox, voy, G.NODE_R, G.EDGE_HIT, G.HOV_HYST, G.CONNECT_R,
        in_view and 1 or 0, over_panel and 1 or 0, over_menu and 1 or 0,
        G.label_epoch or 0, G.nodes_ver or 0, #G.nodes, #G.edges,
        G.dragging or 0, G.connecting or 0,
        G.hovered or 0, G.hov_edge_prev or 0}, ":")
    if hkey ~= G.hover_key then
    local h = (not over_panel and not over_menu and in_view)
              and ops.hit_node(mx, my) or nil
    if not h and G.hovered and not over_panel and not over_menu
       and in_view then
        local n = G.nodes[G.hovered]
        if n then
            local dx = mx - (cb.x + vox + n.x)
            local dy = my - (cb.y + voy + n.y)
            local rr = G.NODE_R + G.HOV_HYST
            if dx * dx + dy * dy < rr * rr then h = G.hovered end
        end
    end
    G.hovered = h
    G.hov_edge = nil
    if not G.hovered and not G.dragging and not G.connecting
       and not over_panel and not over_menu and in_view then
        G.hov_edge = ops.hit_edge(mx, my, G.EDGE_HIT)
        if not G.hov_edge and G.hov_edge_prev
           and G.edges[G.hov_edge_prev]
           and ops.hit_edge_i(G.hov_edge_prev, mx, my,
                              G.EDGE_HIT + G.HOV_HYST) then
            G.hov_edge = G.hov_edge_prev
        end
    end
    G.hov_edge_prev = G.hov_edge

    G.hover_ctx = nil
    if G.dragging then G.hover_ctx = "move"
    elseif G.connecting then G.hover_ctx = "connect"
    elseif not over_panel and not over_menu and in_view then
        if h then
            local n = G.nodes[h]
            local dx = mx - (bx + vox + n.x)
            local dy = my - (by + voy + n.y)
            G.hover_ctx = dx * dx + dy * dy < G.CONNECT_R * G.CONNECT_R
                          and "inner" or "ring"
        elseif G.hov_edge then G.hover_ctx = "edge"
        else G.hover_ctx = "empty" end
    end
        G.hover_key = hkey
    end
    if ops.after_hover then ops.after_hover(G) end

    -- read-only review (Anubis setReadOnly): nodes/edges stay
    -- selectable for inspection but no gesture mutates — no add, no
    -- connect, no move
    local ro = ops.readonly and ops.readonly()

    -- interaction first so a press shows its effect this same frame
    if st == NK.WIDGET_VALID and not over_menu then
        if A.press_in_rect(vx0, vy0, cb.vw, cb.vh) ~= 0 then
            A.clicked_pos(f2)
            local cx, cy = f2[0], f2[1]
            G.press_x, G.press_y = cx, cy
            local inside_panel = (G.selected or G.sel_edge)
                                 and in_rect(cx, cy, G.panel)
            if not inside_panel then
                local hit = ops.hit_node(cx, cy)
                if hit then
                    G.sel_edge = nil
                    local n = G.nodes[hit]
                    local dx = cx - (bx + vox + n.x)
                    local dy = cy - (by + voy + n.y)
                    if not ro
                       and dx * dx + dy * dy < G.CONNECT_R * G.CONNECT_R then
                        G.connecting = hit
                    else
                        G.dragging = hit
                        G.drag_dx = cx - (bx + vox + n.x)
                        G.drag_dy = cy - (by + voy + n.y)
                        G.drag_moved = false
                    end
                else
                    -- prefer the edge the user actually sees
                    -- highlighted: G.hov_edge covers the hover
                    -- hysteresis ring and the label box, which a
                    -- fresh EDGE_HIT retest on the arc alone misses
                    local eh = (G.hov_edge and G.edges[G.hov_edge]
                                and G.hov_edge)
                               or ops.hit_edge(cx, cy, G.EDGE_HIT)
                    if eh then
                        G.selected = nil
                        G.sel_edge = eh
                    elseif G.selected ~= nil or G.sel_edge ~= nil then
                        -- a click elsewhere while the panel is open only
                        -- closes the panel
                        G.selected = nil
                        G.sel_edge = nil
                    elseif not ro then
                        ops.add_node(G,
                            cx - bx - vox,
                            clamp(cy - by, label_margin, bh - G.NODE_R)
                            - voy)
                    end
                end
            end
        end

        if A.mouse_down() ~= 0 and G.dragging and G.nodes[G.dragging] then
            local n = G.nodes[G.dragging]
            if not G.drag_moved then
                local jx = mx - G.press_x
                local jy = my - G.press_y
                if jx * jx + jy * jy >= G.DRAG_TH * G.DRAG_TH then
                    G.drag_moved = true
                end
            end
            if G.drag_moved and not ro then
                local nx2 =
                    clamp(mx - G.drag_dx - bx, G.NODE_R, bw - G.NODE_R)
                    - vox
                local ny2 =
                    clamp(my - G.drag_dy - by, label_margin,
                          bh - G.NODE_R) - voy
                if ops.snap then nx2, ny2 = ops.snap(nx2, ny2, n.id) end
                n.x, n.y = nx2, ny2
            end
        end

        if A.mouse_released() ~= 0 then
            if G.connecting then
                local target = nil
                for i = 1, #G.nodes do
                    if ops.self_loop or i ~= G.connecting then
                        local dx = mx - (bx + vox + G.nodes[i].x)
                        local dy = my - (by + voy + G.nodes[i].y)
                        if dx * dx + dy * dy < G.NODE_R * G.NODE_R then
                            target = i
                            break
                        end
                    end
                end
                if target and not ro then
                    ops.add_edge(G, G.nodes[G.connecting].id,
                                 G.nodes[target].id)
                elseif not ops.self_loop then
                    -- released on the source node: treat as a click
                    local n = G.nodes[G.connecting]
                    local dx = mx - (bx + vox + n.x)
                    local dy = my - (by + voy + n.y)
                    if dx * dx + dy * dy < G.NODE_R * G.NODE_R then
                        G.selected = G.connecting
                        G.sel_edge = nil
                    end
                end
                G.connecting = nil
            end
            if G.dragging then
                if not G.drag_moved then
                    G.selected = G.dragging
                    G.sel_edge = nil
                elseif ops.moved then
                    ops.moved(G, G.dragging)
                end
                G.dragging = nil
            end
            G.drag_moved = false
        end
    end

    -- pointer shape off the hover context (gestures at prio 1)
    if A.set_cursor then
        local id, prio =
            (ops.cursor or default_cursor)(G.hover_ctx, G)
        if id then A.set_cursor(id, prio or 0) end
    end

    -- scissor to the visible viewport (fallback when collapsed)
    if cb.vw > 0 and cb.vh > 0 then
        A.push_scissor(canvas, vx0, vy0, cb.vw, cb.vh)
    else
        A.push_scissor(canvas, bx, by - label_margin, bw,
                       bh + label_margin)
    end

    ops.draw(canvas, {
        G = G, bx = bx, by = by, bw = bw, bh = bh,
        vox = vox, voy = voy,
        vx0 = vx0, vy0 = vy0, vx1 = vx1, vy1 = vy1,
        mx = mx, my = my, fh = fh, label_margin = label_margin,
        over_panel = over_panel, over_menu = over_menu,
        in_view = in_view, ox = ox, oy = oy, ow = ow, oh = oh,
        connect_from = G.connecting and G.nodes[G.connecting] and {
            x = bx + vox + G.nodes[G.connecting].x,
            y = by + voy + G.nodes[G.connecting].y} or nil,
    })

    A.push_scissor(canvas, ox, oy, ow, oh)
end

-- ---------------------------------------------------------------------
-- shared column machinery used by the frames that host gw.widget

-- Scrollbar flags for a scrollable viewport of extent ext_w×ext_h in a
-- client of est_w×est_h: each bar is decided per axis (including the
-- cross-axis cascade when one bar eats 10px of the other), disabled
-- axes get NO_*SCROLLBAR, and a stopped-overflow axis keeps no stale
-- offset in `scroll` (an unsigned int[2]).  Returns flags + the final
-- usable client estimate est_w, est_h.
function gw.view_flags(ext_w, ext_h, est_w, est_h, scroll)
    local need_h = ext_w > est_w
    local need_v = ext_h > est_h
    if need_h and not need_v then
        need_v = ext_h > est_h - 10
    elseif need_v and not need_h then
        need_h = ext_w > est_w - 10
    end
    est_w = est_w - (need_v and 10 or 0)
    est_h = est_h - (need_h and 10 or 0)
    if ext_w <= est_w then scroll[0] = 0 end
    if ext_h <= est_h then scroll[1] = 0 end
    local vflags = NK.WINDOW_BORDER
    if not need_v then vflags = vflags + NK.WINDOW_NO_VSCROLLBAR end
    if not need_h then vflags = vflags + NK.WINDOW_NO_HSCROLLBAR end
    if not (need_v or need_h) then
        vflags = vflags + NK.WINDOW_NO_SCROLLBAR
    end
    return vflags, est_w, est_h
end

gw.SPLIT_W = 8

-- Draggable column splitter: call after row_push(gw.SPLIT_W).  The
-- press must START inside the strip (clicked_pos owns the gesture, so
-- a node drag crossing it is not hijacked), then mouse_pos drives
-- S.split_frac until release.  State lives on the frame's state table:
-- split_frac (fraction of `usable` the left column gets), split_drag,
-- split_rect (this frame's strip bounds); S.menu_open suppresses the
-- cursor change.  lo/hi clamp the fraction, win_x is the frame's
-- client x-origin.
function gw.split_strip(S, usable, win_x, lo, hi)
    if A.widget(f4) == NK.WIDGET_INVALID then return end
    local sx, sy, sw, sh = f4[0], f4[1], f4[2], f4[3]
    S.split_rect = {x = sx, y = sy, w = sw, h = sh}
    A.mouse_pos(f2)
    local mpx, mpy = f2[0], f2[1]
    local function on_strip(x, y)
        return x >= sx - 4 and x < sx + sw + 4
           and y >= sy and y < sy + sh
    end
    local hot = on_strip(mpx, mpy)
    if A.mouse_down() ~= 0 then
        if not S.split_drag then
            A.clicked_pos(f2)
            if on_strip(f2[0], f2[1]) then
                S.split_drag = true
            end
        end
        if S.split_drag then
            S.split_frac = clamp(
                (mpx - win_x - 4 - gw.SPLIT_W * 0.5) / usable, lo, hi)
            hot = true
        end
    else
        S.split_drag = nil
    end
    if hot and not S.menu_open and A.set_cursor then
        A.set_cursor(NKL.CURSOR_RESIZE_H, S.split_drag and 1 or 0)
    end
    -- centre line + grip marks; accent while hovered/dragged
    local cv = A.canvas()
    local lc = hot and TH.BLUE or TH.GREY_DARK
    local cx = sx + sw * 0.5
    A.fill_rect(cv, cx - 1, sy, 2, sh, 0.0, col(lc))
    local gy = sy + sh * 0.5
    for i = -1, 1 do
        A.fill_rect(cv, cx - 1.5, gy + i * 6, 3, 3, 1.0, col(lc))
    end
end

return gw
