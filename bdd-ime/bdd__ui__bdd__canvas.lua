-- ui/bdd/canvas.lua -- the BDD canvas: graphw ops + scene drawing for
-- binary decision diagrams.  Nodes are rounded rectangles (decision,
-- variable label) or plain rectangles (terminal, T/F label); branches
-- are unlabelled, headless polylines — solid for the true/then edge,
-- dotted for the false/else edge, matching the lecture's TikZ style.
--
-- Routing stays deliberately simple (BDDs are drawn top-down, have no
-- loops, no labels to dodge): the straight chord between the two node
-- rims is the default; when it would run through a THIRD node the
-- chord is split around that node's side — a one-pass detour, no
-- fixpoint.  Overlaps between edges themselves are accepted.

local ffi   = require "ffi"
local A     = require "ui.api"
local util  = require "ui.util"
local gen   = require "ui.gen"
local geo   = require "ui.geom"
local gw    = require "ui.graphw"
local G     = require "ui.bdd.state"
local model = require "ui.bdd.model"

local col, pk = util.col, util.pk
local TH = gen.THEME

local C_RED      = {200, 40, 40}
local C_RED_XL   = {255, 242, 242}
local C_AMBER    = {200, 165, 0}
local C_AMBER_XL = {255, 250, 224}
local C_LOCK     = {197, 219, 238}
local C_LOCK_B   = {70, 110, 150}
local C_LOCK_E   = {110, 130, 155}

local H_CLEAR = pk({0, 0, 0, 0})
local bdd = {}
local pbuf = ffi.new("float[256]")

-- ------------------------------------------------------------ node box
-- label width estimate for headless runs (export/tests): ~7px/char
local function label_w(s)
    if A.text_width then return A.text_width(s, -1) end
    -- UTF-8 chars = bytes minus continuation bytes (0x80-0xBF)
    local _, cont = s:gsub("[\128-\191]", "")
    return (#s - cont) * 7
end

-- half-extents: decision nodes grow with their label, terminals stay
-- a small square (the lecture draws T/F in rectangles)
function bdd.node_hw(n, fh)
    local tw = label_w(n.label or "")
    local hw = math.max(G.NODE_HW, tw * 0.5 + 9)
    if n.terminal then return math.min(hw, G.NODE_HW) end
    return hw
end
function bdd.node_hh(n, fh) return G.NODE_HH end

-- clip the segment a->b at the axis-aligned box (cx,cy,hw,hh):
-- returns the parameter t in [0,1] where the ray a->b exits the box
-- (for the source node) or enters it (for the target; use on the
-- reversed direction)
local function box_clip(ax, ay, bx, by, cx, cy, hw, hh)
    local dx, dy = bx - ax, by - ay
    local t = 1.0
    if math.abs(dx) > 1e-9 then
        local tx = (dx > 0 and (cx + hw - ax) or (cx - hw - ax)) / dx
        if tx < t then t = tx end
    end
    if math.abs(dy) > 1e-9 then
        local ty = (dy > 0 and (cy + hh - ay) or (cy - hh - ay)) / dy
        if ty < t then t = ty end
    end
    return math.max(0.0, math.min(1.0, t))
end

-- ----------------------------------------------------------- routing
-- segment (x0,y0)->(x1,y1) vs node box (inflated by `infl`): exact
-- slab intersection — returns the [t0,t1] interval inside the box,
-- or nil.  Blockers are third nodes the edge is not attached to.
local function seg_box_t(x0, y0, x1, y1, k, fh, infl)
    local n = G.nodes[k]
    local hw = bdd.node_hw(n, fh) + (infl or 0)
    local hh = bdd.node_hh(n, fh) + (infl or 0)
    local dx, dy = x1 - x0, y1 - y0
    local t0, t1 = 0.0, 1.0
    for _, ax in ipairs({{dx, x0, n.x, hw}, {dy, y0, n.y, hh}}) do
        local d, o, c, h = ax[1], ax[2], ax[3], ax[4]
        if math.abs(d) < 1e-9 then
            if math.abs(o - c) >= h then return nil end
        else
            local ta, tb = (c - h - o) / d, (c + h - o) / d
            if ta > tb then ta, tb = tb, ta end
            if ta > t0 then t0 = ta end
            if tb < t1 then t1 = tb end
        end
    end
    if t0 >= t1 then return nil end
    return t0, t1
end

-- detour around blocker k: the chord is split into a 3-leg bump
-- around the box corner on the side that deviates least.  Two
-- waypoints at the entry/exit parameters pushed out through the
-- chosen face, so each leg provably clears the inflated box.
local function dodge_wps(x0, y0, x1, y1, k, fh, infl)
    local n = G.nodes[k]
    local t0, t1 = seg_box_t(x0, y0, x1, y1, k, fh, infl or 0)
    if not t0 then return nil end
    local hw = bdd.node_hw(n, fh) + (infl or 0)
    local hh = bdd.node_hh(n, fh) + (infl or 0)
    local px = x0 + (x1 - x0) * (t0 + t1) * 0.5
    local py = y0 + (y1 - y0) * (t0 + t1) * 0.5
    -- candidate faces: exit through the side nearest the chord
    local cands = {
        {n.x - hw, py, n.x - hw, py},      -- left face is a point pair
        {n.x + hw, py, n.x + hw, py},
        {px, n.y - hh, px, n.y - hh},
        {px, n.y + hh, px, n.y + hh},
    }
    -- proper corner bump: waypoint pair = box face corners offset
    local function bump(side)
        local ax, ay, bx, by
        local ex = x0 + (x1 - x0) * t0
        local ey = y0 + (y1 - y0) * t0
        local fx = x0 + (x1 - x0) * t1
        local fy = y0 + (y1 - y0) * t1
        if side == 1 then      -- left
            ax, ay = n.x - hw, ey
            bx, by = n.x - hw, fy
        elseif side == 2 then  -- right
            ax, ay = n.x + hw, ey
            bx, by = n.x + hw, fy
        elseif side == 3 then  -- above
            ax, ay = ex, n.y - hh
            bx, by = fx, n.y - hh
        else                   -- below
            ax, ay = ex, n.y + hh
            bx, by = fx, n.y + hh
        end
        return ax, ay, bx, by
    end
    local best, bd = nil, math.huge
    for side = 1, 4 do
        local ax, ay, bx, by = bump(side)
        local ok = not seg_box_t(x0, y0, ax, ay, k, fh, infl)
               and not seg_box_t(bx, by, x1, y1, k, fh, infl)
        local len = math.abs(ax - x0) + math.abs(ay - y0)
                  + math.abs(bx - ax) + math.abs(by - ay)
                  + math.abs(x1 - bx) + math.abs(y1 - by)
        if ok and len < bd then best, bd = {ax, ay, bx, by}, len end
    end
    -- all four faces still graze (odd angle): take the shortest bump
    if not best then
        for side = 1, 4 do
            local ax, ay, bx, by = bump(side)
            local len = math.abs(ax - x0) + math.abs(ay - y0)
                      + math.abs(bx - ax) + math.abs(by - ay)
                      + math.abs(x1 - bx) + math.abs(y1 - by)
            if len < bd then best, bd = {ax, ay, bx, by}, len end
        end
    end
    return best
end

-- the resolved route of edge i in MODEL coords (bx/by/vox/voy = 0) or
-- screen coords; returns flat {x0,y0,x1,y1,...} with endpoints on the
-- node rims, detouring around blocking nodes.  Two passes: a first
-- detour can land inside a second blocker — re-check once.
function bdd.edge_poly(i, bx, by, vox, voy, fh)
    local e = G.edges[i]
    local ai, bi = model.find_node(G, e.from), model.find_node(G, e.to)
    if not (ai and bi) or ai == bi then return nil end
    local n1, n2 = G.nodes[ai], G.nodes[bi]
    local x0, y0 = n1.x, n1.y
    local x1, y1 = n2.x, n2.y
    -- endpoints on the rims (clip at each endpoint's own box)
    local t0 = box_clip(x0, y0, x1, y1, n1.x, n1.y,
                        bdd.node_hw(n1, fh), bdd.node_hh(n1, fh))
    local t1 = box_clip(x1, y1, x0, y0, n2.x, n2.y,
                        bdd.node_hw(n2, fh), bdd.node_hh(n2, fh))
    x1, y1 = x1 + (x0 - x1) * t1, y1 + (y0 - y1) * t1
    x0, y0 = x0 + (x1 - x0) * t0, y0 + (y1 - y0) * t0
    local pts = {x0, y0, x1, y1}
    -- parallel branches between the same pair (e.g. a spurious node
    -- feeding T twice) would collapse onto one chord — fan the rim
    -- attachment points apart so both stay visible
    local sib_n, sib_i = 0, 0
    for j = 1, #G.edges do
        local e2 = G.edges[j]
        if e2.from == e.from and e2.to == e.to then
            sib_n = sib_n + 1
            if j == i then sib_i = sib_n end
        end
    end
    if sib_n > 1 then
        local d = (sib_i - (sib_n + 1) * 0.5) * 11
        pts[1] = pts[1] + d
        pts[#pts - 1] = pts[#pts - 1] + d
    end
    -- dodge: while a third node overlaps a leg, split that leg into a
    -- two-waypoint bump around the blocker (bounded passes)
    for _ = 1, 6 do
        local inserted = false
        for k = 1, #G.nodes do
            if k ~= ai and k ~= bi then
                local s = 1
                while s + 3 <= #pts do
                    local ax, ay, bx2, by2 =
                        pts[s], pts[s + 1], pts[s + 2], pts[s + 3]
                    if seg_box_t(ax, ay, bx2, by2, k, fh, 3) then
                        local wp = dodge_wps(ax, ay, bx2, by2, k, fh, 3)
                        if wp then
                            for w = #wp, 1, -1 do
                                table.insert(pts, s + 2, wp[w])
                            end
                            inserted = true
                            break
                        end
                    end
                    s = s + 2
                end
            end
            if inserted then break end
        end
        if not inserted then break end
    end
    -- to screen coords
    local ox, oy = (bx or 0) + (vox or 0), (by or 0) + (voy or 0)
    if ox ~= 0 or oy ~= 0 then
        for k = 1, #pts, 2 do
            pts[k], pts[k + 1] = pts[k] + ox, pts[k + 1] + oy
        end
    end
    return pts
end

-- --------------------------------------------------------- validity
-- cheap local flags (no server): >2 branches or a duplicate kind off
-- one decision node, a branch out of a terminal, a cycle.  Marked
-- nodes/edges get the red/amber problem colours in the scene.
local function validate(fh)
    G.prob_nodes, G.prob_edges = nil, nil
    local out, kind = {}, {}
    for _, e in ipairs(G.edges) do
        out[e.from] = (out[e.from] or 0) + 1
        local sig = e.from .. ":" .. (e.low and "L" or "H")
        if kind[sig] then
            G.prob_edges = G.prob_edges or {}
            G.prob_edges[e.id] = "error"
            G.prob_edges[kind[sig]] = "error"
            G.prob_nodes = G.prob_nodes or {}
            G.prob_nodes[e.from] = "error"
        else
            kind[sig] = e.id
        end
    end
    for _, n in ipairs(G.nodes) do
        local o = out[n.id] or 0
        if n.note and o > 0 then
            G.prob_nodes = G.prob_nodes or {}
            G.prob_nodes[n.id] = "error"
        elseif n.note then
            -- annotation text: never a validation target
        elseif n.terminal and o > 0 then
            G.prob_nodes = G.prob_nodes or {}
            G.prob_nodes[n.id] = "error"
        elseif not n.terminal and o > 2 then
            G.prob_nodes = G.prob_nodes or {}
            G.prob_nodes[n.id] = "error"
        end
    end
    -- cycle check (DFS on the directed graph)
    local adj = {}
    for _, e in ipairs(G.edges) do
        adj[e.from] = adj[e.from] or {}
        adj[e.from][#adj[e.from] + 1] = e.to
    end
    local mark = {}   -- 1 = in stack, 2 = done
    local cyclic = {}
    local function dfs(u)
        mark[u] = 1
        for _, v in ipairs(adj[u] or {}) do
            if mark[v] == 1 then cyclic[u], cyclic[v] = true, true
            elseif mark[v] == nil then dfs(v) end
        end
        mark[u] = 2
    end
    for _, n in ipairs(G.nodes) do
        if not mark[n.id] then dfs(n.id) end
    end
    for id in pairs(cyclic) do
        G.prob_nodes = G.prob_nodes or {}
        G.prob_nodes[id] = G.prob_nodes[id] or "error"
    end
end

-- -------------------------------------------------------- hit tests
-- (screen coords — the skeleton passes pointer positions; model space
-- sits behind the canvas origin + view offset)
local function hit_node(px, py)
    local cb = G.canvas
    for i = #G.nodes, 1, -1 do
        local n = G.nodes[i]
        local hw = bdd.node_hw(n) + 2
        local hh = bdd.node_hh(n) + 2
        local dx = px - (cb.x + (cb.ox or 0) + n.x)
        local dy = py - (cb.y + (cb.oy or 0) + n.y)
        if math.abs(dx) <= hw and math.abs(dy) <= hh then
            return i
        end
    end
    return nil
end

local function hit_edge_i(i, px, py, halfw)
    local cb = G.canvas
    local pts = bdd.edge_poly(i, cb.x, cb.y,
                              cb.ox or 0, cb.oy or 0, 14)
    if not pts then return false end
    return geo.poly_dist(pts, px, py) <= (halfw or G.EDGE_HIT)
end

local function hit_edge(px, py, halfw)
    for i = #G.edges, 1, -1 do
        if hit_edge_i(i, px, py, halfw) then return i end
    end
    return nil
end

-- ------------------------------------------------------------ scene
-- dots along a polyline (the lecture's "dotted" else branch)
local function dot_poly(canvas, pts, w, c, spacing)
    local step = spacing or 7
    local r = w * 0.9
    local carry = 0
    for s = 1, #pts - 2, 2 do
        local ax, ay, bx, by = pts[s], pts[s + 1], pts[s + 2], pts[s + 3]
        local dx, dy = bx - ax, by - ay
        local len = math.sqrt(dx * dx + dy * dy)
        if len > 1e-6 then
            local ux, uy = dx / len, dy / len
            local d = step - carry
            while d <= len do
                local px, py = ax + ux * d, ay + uy * d
                A.fill_circle(canvas, px - r, py - r, r * 2, r * 2,
                              col(c))
                d = d + step
            end
            carry = (len - (d - step)) % step
            if carry < 0 then carry = 0 end
            carry = step - ((d - step) - len)
            if carry >= step or carry < 0 then carry = 0 end
        end
    end
end

local function bdd_draw(canvas, ctx)
    local cb = G.canvas
    local bx, by = ctx.bx, ctx.by
    local vox, voy = ctx.vox, ctx.voy
    local mx, my, fh = ctx.mx, ctx.my, ctx.fh

    A.fill_rect(canvas, ctx.vx0, ctx.vy0, cb.vw, cb.vh, 0.0,
                col(TH.GREY_XLIGHT))
    A.stroke_rect(canvas, ctx.vx0, ctx.vy0, cb.vw, cb.vh, 0.0, 1.0,
                  col(TH.GREY_LIGHT))

    validate(fh)

    -- edges first so nodes paint over branch ends
    for i = 1, #G.edges do
        local pts = bdd.edge_poly(i, bx, by, vox, voy, fh)
        if pts then
            local e = G.edges[i]
            local sel = (G.sel_edge == i)
            local hov = (G.hov_edge == i)
            local pr = G.prob_edges and G.prob_edges[e.id]
            local ec = pr == "error" and C_RED
                       or pr and C_AMBER
                       or (sel or hov) and TH.BLUE
                       or (e.locked and C_LOCK_E or TH.GREY_DARK)
            local n = #pts / 2
            if e.low then
                dot_poly(canvas, pts, 2.0, ec)
            else
                for j = 1, #pts do pbuf[j - 1] = pts[j] end
                A.stroke_polyline(canvas, pbuf, n,
                                  sel and 3.5 or (hov and 2.5 or 2.0),
                                  pk(ec))
            end
        end
    end

    -- connect gesture: straight preview ray
    if G.connecting and ctx.connect_from then
        gw.connect_preview(canvas, ctx)
    end

    for i = 1, #G.nodes do
        local n = G.nodes[i]
        local nx, ny = bx + vox + n.x, by + voy + n.y
        local hw = bdd.node_hw(n, fh)
        local hh = bdd.node_hh(n, fh)
        if nx + hw + 6 >= ctx.vx0 and nx - hw - 6 <= ctx.vx1
           and ny + hh + 6 >= ctx.vy0 and ny - hh - 6 <= ctx.vy1 then
        local on_handle = false
        if i == G.hovered and mx then
            local dx, dy = mx - nx, my - ny
            on_handle = dx * dx + dy * dy < G.CONNECT_R * G.CONNECT_R
        end
        local fill, border, handle =
            TH.WHITE, TH.GREY_DARK, TH.GREY_LIGHT
        if n.locked then fill, border = C_LOCK, C_LOCK_B end
        if i == G.hovered then fill = TH.GREY_XLIGHT end
        local pr = G.prob_nodes and G.prob_nodes[n.id]
        if pr == "error" then
            fill, border = C_RED_XL, C_RED
        elseif pr then
            fill, border = C_AMBER_XL, C_AMBER
        end
        if i == G.selected then
            border = TH.DARKBLUE
            if not pr then fill = TH.BLUE end
        end
        if G.connecting and i == G.hovered then
            border = TH.BLUE
        end
        if on_handle then handle = TH.BLUE end

        -- decision node: rounded rect; terminal: plain rect;
        -- annotation node: bare text (no box)
        if not n.note then
            local rounding = n.terminal and 0.0 or hh * 0.65
            A.fill_rect(canvas, nx - hw, ny - hh, hw * 2, hh * 2,
                        rounding, col(fill))
            A.stroke_rect(canvas, nx - hw, ny - hh, hw * 2, hh * 2,
                          rounding, i == G.selected and 3.0 or 1.8,
                          col(border))
        elseif i == G.selected or i == G.hovered then
            -- notes have no box: a hairline shows what was picked
            A.stroke_rect(canvas, nx - hw, ny - hh, hw * 2, hh * 2,
                          2.0, 1.0, col(border))
        end
        if i == G.hovered and not G.connecting then
            A.stroke_circle(canvas, nx - G.CONNECT_R, ny - G.CONNECT_R,
                            G.CONNECT_R * 2, G.CONNECT_R * 2, 1.0,
                            col(TH.GREY))
        end
        if i == G.hovered then
            A.fill_circle(canvas, nx - G.NODE_C, ny - G.NODE_C,
                          G.NODE_C * 2, G.NODE_C * 2, col(handle))
            A.stroke_circle(canvas, nx - G.NODE_C, ny - G.NODE_C,
                            G.NODE_C * 2, G.NODE_C * 2, 1.0,
                            col(TH.GREY_DARK))
        end
        local label = n.label
        if label == "" and not n.terminal then label = "?" end
        if label ~= "" then
            local tw = A.text_width(label, -1)
            local tc = (i == G.selected and not pr) and TH.WHITE
                       or TH.BLACK
            A.draw_text(canvas, nx - tw * 0.5, ny - fh * 0.5, tw, fh,
                        label, -1, H_CLEAR, pk(tc))
        end
        end
    end
end

-- -------------------------------------------------------------- grid
local function snap_pt(x, y)
    local g = G.GRID or 66.0
    return math.max(g, math.floor(x / g + 0.5) * g),
           math.max(g, math.floor(y / g + 0.5) * g)
end

local function occ_cells(except_id)
    local occ = {}
    for _, n in ipairs(G.nodes) do
        if n.id ~= except_id then
            local cx, cy = snap_pt(n.x, n.y)
            occ[cx .. "," .. cy] = true
        end
    end
    return occ
end

local function snap_free(x, y, except_id)
    local g = G.GRID or 66.0
    local sx, sy = snap_pt(x, y)
    local occ = occ_cells(except_id)
    if not occ[sx .. "," .. sy] then return sx, sy end
    for r = 1, 8 do
        local fx, fy, fd
        for dy = -r, r do
            for dx = -r, r do
                if math.max(math.abs(dx), math.abs(dy)) == r then
                    local cx, cy = sx + dx * g, sy + dy * g
                    if cx >= g and cy >= g
                            and not occ[cx .. "," .. cy] then
                        local d = dx * dx + dy * dy
                        if not fd or d < fd then
                            fx, fy, fd = cx, cy, d
                        end
                    end
                end
            end
        end
        if fx then return fx, fy end
    end
    return sx, sy
end

local BDD_OPS = {
    hit_node = hit_node,
    hit_edge = hit_edge,
    hit_edge_i = hit_edge_i,
    add_node = function(_, x, y)
        model.add_node(G, snap_free(x, y))
    end,
    add_edge = function(_, from, to) model.add_edge(G, from, to) end,
    moved = function()
        if model.on_changed then model.on_changed() end
    end,
    snap = snap_free,
    self_loop = false,     -- a DAG has no self edges
    draw = bdd_draw,
    readonly = function() return G.readonly end,
    cursor = function(ctx, S)
        if G.readonly then return nil end
        return gw.default_cursor(ctx, S)
    end,
}

function bdd.widget(height, width)
    return gw.widget(height, width, G, BDD_OPS)
end

function bdd.destack()
    for _, n in ipairs(G.nodes) do
        local cx, cy = snap_pt(n.x, n.y)
        if occ_cells(n.id)[cx .. "," .. cy] then
            n.x, n.y = snap_free(n.x, n.y, n.id)
        end
    end
end
G.destack = bdd.destack

bdd.hit_node   = hit_node
bdd.hit_edge   = hit_edge
bdd.hit_edge_i = hit_edge_i
bdd.ops        = BDD_OPS
return bdd
