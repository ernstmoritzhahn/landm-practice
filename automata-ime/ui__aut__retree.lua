-- ui/aut/retree.lua -- the regular expression's syntax tree, drawn
-- into the workspace's scrolled tree group.  A didactic view of the
-- expression's structure, not a primary editing surface: leaves are
-- the literals (symbols, lambda, empty set), inner nodes the
-- operators (union/concat/star/plus).  Clicking a node selects its
-- source span in the expression field (the reverse direction --
-- caret -> deepest covering node -- is resolved in ui/aut/re.lua and
-- arrives here as the `active` node).

local ffi  = require "ffi"
local A    = require "ui.api"
local util = require "ui.util"
local gen  = require "ui.gen"

local f4 = ffi.new("float[4]")
local f2 = ffi.new("float[2]")

local NK = gen.NK

local pk, col = util.pk, util.col
local TH = gen.THEME

local retree = {}

-- node circle radius / grid pitch (scaled by the caller's s)
retree.R  = 15.0
retree.DX = 56.0
retree.DY = 62.0

local LABEL = {union = "\xE2\x88\xAA",        -- ∪
               cat   = "\xC2\xB7",            -- ·
               star  = "*", plus = "+",
               eps   = "\xCE\xBB",            -- λ
               empty = "\xE2\x88\x85"}        -- ∅

local function kids_of(n)
    return n.kids or (n.kid and {n.kid}) or nil
end

-- tidy layout: leaves take successive x slots, inner nodes centre
-- over their children, rows are depths.  Returns node -> {x,y}
-- (already in pixels, origin at the tree's top-left) plus the
-- extent in pixels.  Exported: the caller preflights the extent for
-- the scroll group, draw() reuses the same positions.
function retree.layout(ast, dx, dy, r)
    local pos, leaf, maxrow = {}, 0, 0
    local function walk(n, d)
        if d > maxrow then maxrow = d end
        local ks = kids_of(n)
        if not ks or #ks == 0 then
            pos[n] = {x = leaf, y = d}
            leaf = leaf + 1
        else
            for _, k in ipairs(ks) do walk(k, d + 1) end
            pos[n] = {x = (pos[ks[1]].x + pos[ks[#ks]].x) / 2, y = d}
        end
    end
    walk(ast, 0)
    local pad = r + 6
    for n, p in pairs(pos) do
        p.x = pad + p.x * dx
        p.y = pad + p.y * dy
    end
    return pos,
           math.max(1, leaf - 1) * dx + 2 * pad,
           maxrow * dy + 2 * pad
end

local function node_text(n)
    return n.t == "sym" and n.s or LABEL[n.t] or "?"
end

-- draw the tree inside a widget of the given pixel extent, centred
-- horizontally in the visible width when it fits.  `active` (an AST
-- node table) gets the selection colour; a click on a node reports
-- it through retree.clicked for the caller's span selection.
function retree.draw(ast, active, vw, vh, s)
    if not ast then return 0, 0 end
    local r  = retree.R  * s
    local dx = retree.DX * s
    local dy = retree.DY * s
    local pos, ext_w, ext_h = retree.layout(ast, dx, dy, r)
    local w = math.max(vw, ext_w)
    local h = math.max(vh, ext_h)
    A.row_begin(NK.STATIC, h, 1)
    A.row_push(w)
    local st = A.widget(f4)
    A.row_end()
    if st == NK.WIDGET_INVALID then return ext_w, ext_h end
    local canvas = A.canvas()
    local ox = f4[0] + math.max(0, (vw - ext_w) / 2)
    local oy = f4[1]
    retree.clicked = nil
    retree.hovered = nil
    -- window-absolute node centres for tests/debug clicks (AUT_DUMP_NODES)
    retree.last = {pos = pos, ox = ox, oy = oy}

    -- edges first (under the node circles)
    local function edges(n)
        local ks = kids_of(n)
        if ks then
            for _, k in ipairs(ks) do
                A.stroke_line(canvas,
                              ox + pos[n].x, oy + pos[n].y,
                              ox + pos[k].x, oy + pos[k].y,
                              1.5, col(TH.GREY_DARK))
                edges(k)
            end
        end
    end
    edges(ast)

    -- hit test happens during the same pass: mouse and click
    -- positions are window-absolute like the widget bounds
    local clicked = A.press_in_rect(f4[0], f4[1], f4[2], f4[3]) ~= 0
    A.mouse_pos(f2)
    local mx, my = f2[0], f2[1]
    if clicked then
        A.clicked_pos(f2)
        mx, my = f2[0], f2[1]
    end
    local inside = mx >= f4[0] and mx < f4[0] + f4[2]
               and my >= f4[1] and my < f4[1] + f4[3]

    local fh = A.font_height()
    local function nodes(n)
        local x, y = ox + pos[n].x, oy + pos[n].y
        if inside and not retree.hovered
           and (mx - x) * (mx - x) + (my - y) * (my - y)
               <= r * r * 1.44 then
            retree.hovered = n
            if clicked and not retree.clicked then
                retree.clicked = n
            end
        end
        local on  = (n == active)
        local hov = (n == retree.hovered) and not on
        A.fill_circle(canvas, x - r, y - r, r * 2, r * 2,
                      col(on and {226, 238, 252}
                          or hov and {240, 246, 252}
                          or {255, 255, 255}))
        A.stroke_circle(canvas, x - r, y - r, r * 2, r * 2,
                        on and 2.5 or hov and 2.0 or 1.5,
                        col(on and TH.BLUE
                            or hov and {110, 140, 180}
                            or TH.GREY_DARK))
        local t = node_text(n)
        local tw = A.text_width(t, -1)
        A.draw_text(canvas, x - tw / 2, y - fh / 2, tw, fh,
                    t, -1, 0, pk(TH.BLACK))
        local ks = kids_of(n)
        if ks then for _, k in ipairs(ks) do nodes(k) end end
    end
    nodes(ast)
    return ext_w, ext_h
end

return retree
