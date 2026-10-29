-- ui/aut/canvas.lua -- the automaton canvas: graphw ops + scene drawing
-- for state/transition editing.  Directed transitions route as
-- tessellated circular arcs (bowed apart when edges share a
-- direction or a pair runs both ways), self-transitions are circle arcs
-- of a loop circle meeting the rim at ±psi.  The same flat polyline
-- feeds stroke_polyline, the hit tests
-- and the arrowhead tangent, so the three can never disagree.

local ffi   = require "ffi"
local A     = require "ui.api"
local util  = require "ui.util"
local gen   = require "ui.gen"
local geo   = require "ui.geom"
local gw    = require "ui.graphw"
local G     = require "ui.aut.state"
local model = require "ui.aut.model"

local col, pk = util.col, util.pk
local TH = gen.THEME

-- validation severity palette (same values the BN tool reports with)
local C_RED      = {200, 40, 40}
local C_RED_XL   = {255, 242, 242}
local C_AMBER    = {200, 165, 0}
local C_AMBER_XL = {255, 250, 224}
-- locked components (guided composition): pale navy fill + steel-navy
-- border/transitions — visually distinct from the student's elements
local C_LOCK     = {197, 219, 238}
local C_LOCK_B   = {70, 110, 150}
local C_LOCK_E   = {110, 130, 155}
-- dashed grey markers for a locked component's own entry/exit states
local C_SEED_MK  = {120, 135, 155}
local C_SIM      = {205, 238, 222}   -- live sim config: pale teal
local C_SIM_E    = {0, 148, 108}     -- sim transition just taken

local aut = {}
local in_clear = false   -- dodge-clearance recursion guard
local DBG_EDGE = os.getenv and tonumber(os.getenv("DBG_EDGE") or "")

-- resolved label boxes + routes of earlier edges in the SAME scene:
-- edge i's clearance and label placement must see what earlier edges
-- actually resolved to, not their base geometry — otherwise two
-- family members can collapse onto the same arc.  The caches are
-- keyed on a scene signature so any layout/model change drops them
local lbl_sig, lbl_pos, route_res, route_bb = nil, {}, {}, {}

-- fwd-declared: defined just below label_viol's use, referenced
-- earlier by resolve_all's scoped fixpoint
local poly_bb, rect_bb_dist
local refined = false   -- fixpoint pass already ran for this scene
local drag_settle = false  -- released drag: force a full re-resolve
local keep_route = nil  -- prior route fed into a re-resolution scan
local drag_was = false  -- last frame was a drag: settle once fully
local prev_scene = nil  -- last model snapshot for scoped diffs
local fp_seed = nil     -- fixpoint seed bbs; nil = full resweep
local kept_hyst = nil   -- j -> {poly,bb}: prior routes of dirty edges

-- candidate reach of edge j: every route the scan can produce stays
-- inside the chord's bbox inflated by the deepest bow (0.55*dl arcs)
-- or the via-corridor (blockers up to NODE_R+80 off the chord plus
-- pockets another NODE_R+50 beyond).  An edge's resolution cannot
-- change while nothing inside this rect moved — the basis both of
-- the scoped fixpoint below and of scene-change scoped dirtying
local function edge_reach(j, bx, by, vox, voy)
    local e = G.edges[j]
    local ai2, bi2 = model.find_state(G, e.from),
                     model.find_state(G, e.to)
    if not (ai2 and bi2) or ai2 == bi2 then
        -- loops reach far around their state — never prune them
        return {-1e9, -1e9, 1e9, 1e9}
    end
    local n1, n2 = G.nodes[ai2], G.nodes[bi2]
    local x0, y0 = bx + vox + n1.x, by + voy + n1.y
    local x1, y1 = bx + vox + n2.x, by + voy + n2.y
    local R = math.max(math.sqrt((x1 - x0) ^ 2 + (y1 - y0) ^ 2) * 0.55,
                       2 * G.NODE_R + 130) + 10
    return {math.min(x0, x1) - R, math.min(y0, y1) - R,
            math.max(x0, x1) + R, math.max(y0, y1) + R}
end
local function scene_sig(bx, by, vox, voy, fh)
    local t = {bx, by, vox or 0, voy or 0, fh or 0}
    for _, n in ipairs(G.nodes) do
        t[#t + 1] = string.format("%d:%.1f,%.1f", n.id, n.x, n.y)
    end
    for _, e in ipairs(G.edges) do
        t[#t + 1] = e.from .. ">" .. e.to .. "=" .. (e.label or "")
    end
    return table.concat(t, "|")
end

-- resolve every edge's route, then re-resolve once more: in the
-- first sweep an edge sees only the BASE geometry of siblings that
-- resolve after it, and a phantom conflict there can push it into a
-- needlessly deep route.  The second sweep (Gauss-Seidel, index
-- order) re-routes each edge against the REAL routes of all the
-- others — order artefacts wash out and e.g. a long single finds its
-- shallow wire even when it was created before the edges it threads
-- resolution ORDER matters: an edge's candidate scan snapshots its
-- siblings' routes and unresolved siblings appear as base geometry.
-- Families (bidirectional pairs, same-direction fans) and loops are
-- structural — they resolve first, in index order.  TRUE singles
-- resolve last: they must see every real sibling route to thread
-- the corridors between them, and they alone may flip sides
local function resolve_all(bx, by, vox, voy, fh)
    for pass = 1, 2 do
        for j = 1, #G.edges do
            local ej = G.edges[j]
            local single = false
            if ej.from ~= ej.to then
                -- aut.edge_siblings resolves at call time (the local
                -- is declared further down this file)
                local _, nf, nr = aut.edge_siblings(j)
                single = nr == 0 and nf <= 1
            end
            if (pass == 2) == single and not route_res[j] then
                -- a dirty edge in a scoped scene still has its prior
                -- route: feed it as hysteresis (stable pictures) and
                -- seed the fixpoint with the delta it actually made
                local kp = kept_hyst and kept_hyst[j]
                keep_route = kp and kp.poly or nil
                aut.edge_poly(j, bx, by, vox, voy, fh, true)
                keep_route = nil
                if fp_seed then
                    local new, obb = route_res[j], kp and kp.bb
                    if kp then
                        if new then
                            local dm = 0
                            for k = 1, math.max(#kp.poly, #new) do
                                local d = math.abs((kp.poly[k] or 0)
                                                   - (new[k] or 0))
                                if d > dm then dm = d end
                            end
                            if dm > 0.5 then
                                fp_seed[#fp_seed + 1] = obb
                                fp_seed[#fp_seed + 1] = route_bb[j]
                            end
                        end
                    elseif route_bb[j] then
                        -- genuinely new route (added/rewired edge):
                        -- it occupies space nobody saw before
                        fp_seed[#fp_seed + 1] = route_bb[j]
                    end
                end
            end
        end
    end
    -- refinement: the first pass scored candidates against the PHANTOM
    -- base geometry of not-yet-resolved siblings — dodging wires that
    -- never materialise.  Re-resolve every edge against the now
    -- complete set of real routes until nothing moves (bounded:
    -- order artefacts converge fast, oscillation is cut off)
    -- refinement runs once per scene (resolve_all fires on every
    -- label placement AND once per frame at draw start), only when
    -- every edge holds a route, and never against STALE routes —
    -- route_res is wiped when lbl_sig changes, anything before that
    -- belongs to the previous scene.  While a state is being dragged
    -- the signature changes EVERY frame — defer the resweep to the
    -- settle frame or every drag frame costs a full re-resolution
    if refined or G.dragging
       or scene_sig(bx, by, vox, voy, fh) ~= lbl_sig then
        return
    end
    for j = 1, #G.edges do
        if not route_res[j] then return end
    end
    refined = true
    -- candidate reach: every route the scan can produce stays inside
    -- the chord's bbox inflated by the deepest bow (0.55*dl arcs) or
    -- the via-corridor (blockers up to NODE_R+80 off the chord plus
    -- pockets another NODE_R+50 beyond).  An edge re-resolves
    -- identically while no foreign route inside that reach moved —
    -- so after the first sweep only edges touching last iteration's
    -- moved bboxes (old AND new positions) get another scan
    local reach = {}
    local function reach_rect(j)
        local r = reach[j]
        if not r then r = edge_reach(j, bx, by, vox, voy); reach[j] = r end
        return r
    end
    -- seed: in a scoped scene only the changed regions (and whatever
    -- the dirty edges really moved) can push routes — everywhere
    -- else the cached resolution is provably identical.  nil means
    -- "fresh scene" → the classic full resweep of iteration 1
    local moved_bb = fp_seed
    fp_seed, kept_hyst = nil, nil
    local DBG_ITER = os.getenv("DBG_ITER") == "1"
    for iter = 1, 3 do
        local changed = false
        local moved = {}
        for j = 1, #G.edges do
            local old = route_res[j]
            local rescan = not moved_bb
            if not rescan then
                local r = reach_rect(j)
                for _, mb in ipairs(moved_bb) do
                    if rect_bb_dist(r[1], r[2], r[3], r[4], mb) <= 9
                    then
                        rescan = true; break
                    end
                end
            end
            if old and rescan then
                local obb = route_bb[j] or poly_bb(old)
                route_res[j], route_bb[j] = nil, nil
                keep_route = old
                aut.edge_poly(j, bx, by, vox, voy, fh, true)
                keep_route = nil
                local new = route_res[j] or old
                local dmax = 0
                for k = 1, math.max(#old, #new) do
                    local d = math.abs((old[k] or 0) - (new[k] or 0))
                    if d > dmax then dmax = d end
                end
                if dmax > 0.5 then
                    changed = true
                    moved[#moved + 1] = obb
                    moved[#moved + 1] =
                        route_bb[j] or poly_bb(new)
                    if DBG_ITER then
                        print(string.format(
                            "    e%d moved %.1f", j, dmax))
                    end
                end
            end
        end
        moved_bb = moved
        if DBG_ITER then
            print("  iter", iter, "changed:", changed)
        end
        if not changed then break end
    end
end

-- growable float buffer for stroke_polyline
local pbuf, pbuf_n = nil, 0
local function pbuf_for(nfloats)
    if pbuf_n < nfloats then
        pbuf_n = math.max(256, nfloats * 2)
        pbuf = ffi.new("float[?]", pbuf_n)
    end
    return pbuf
end

-- sibling geometry for edge i: k = its index among the (from,to) group,
-- nf = group size, nr = edges running the other way, br = index among
-- the BIDIRECTIONAL family (both directions, edge order) — the nested
-- fan is spread by br, not k: two opposite edges with the same k used
-- to get identical attach angles and drew the exact same arc
local function edge_siblings(i)
    local e = G.edges[i]
    local nf, nr, k, br = 0, 0, 0, 0
    for j, ej in ipairs(G.edges) do
        if ej.from == e.from and ej.to == e.to then
            nf = nf + 1
            if j <= i then k = k + 1 end
        elseif ej.from == e.to and ej.to == e.from then
            nr = nr + 1
        end
        if (ej.from == e.from and ej.to == e.to)
           or (ej.from == e.to and ej.to == e.from) then
            if j <= i then br = br + 1 end
        end
    end
    return k, nf, nr, br
end

-- flat screen-space polyline for edge i plus a label anchor point
-- (text CENTRE: offset past the curve's outer side so labels never sit
-- on the line).  nil when an endpoint is gone.
local LBL_OFF = 10.0   -- label-centre distance beyond the curve

-- score a label box CENTRE (lx,ly,tw×fh): state discs weigh most,
-- then every stroke (own edge included — a label must never sit on a
-- line), then the base anchors of foreign labels.  Positive always;
-- the candidate search picks the cheapest legal site
-- axis-aligned bbox of a flat polyline
function poly_bb(q)
    local x0, y0, x1, y1 = q[1], q[2], q[1], q[2]
    for k = 3, #q, 2 do
        local x, y = q[k], q[k + 1]
        if x < x0 then x0 = x elseif x > x1 then x1 = x end
        if y < y0 then y0 = y elseif y > y1 then y1 = y end
    end
    return {x0, y0, x1, y1}
end

-- gap distance rect (x0,y0,x1,y1) vs poly bbox — poly cannot be
-- closer than its bbox, so a positive gap prunes the seg loop
function rect_bb_dist(rx0, ry0, rx1, ry1, bb)
    local dx = math.max(bb[1] - rx1, rx0 - bb[3], 0)
    local dy = math.max(bb[2] - ry1, ry0 - bb[4], 0)
    if dx == 0 and dy == 0 then return 0 end
    return math.sqrt(dx * dx + dy * dy)
end

local function label_viol(i, bx, by, vox, voy, lx, ly, tw, fh)
    local v = 0
    for _, n in ipairs(G.nodes) do
        local d = geo.rect_pt_dist(lx - tw * 0.5, ly - fh * 0.5,
            tw, fh, bx + vox + n.x, by + voy + n.y)
        if d < G.NODE_R + 1 then
            v = v + 100 + (G.NODE_R + 1 - d)
        end
    end
    for j = 1, #G.edges do
        -- in_clear makes the nested call return BASE geometry cheaply;
        -- resolved routes come from the scene cache instead — never
        -- re-run a sibling's full search while placing our label
        local wc = in_clear
        in_clear = true
        local q, ax3, ay3 = aut.edge_poly(j, bx, by, vox, voy,
                                        nil, true)
        in_clear = wc
        q = route_res[j] or q
        if q then
            local bb = route_bb[j]
            if not bb then
                bb = poly_bb(q)
                route_bb[j] = bb
            end
            if rect_bb_dist(lx - tw * 0.5, ly - fh * 0.5,
                            lx + tw * 0.5, ly + fh * 0.5, bb) <= 0.5
            then
                for k2 = 1, #q - 2, 2 do
                    local d = geo.rect_seg_dist(lx - tw * 0.5,
                        ly - fh * 0.5, tw, fh,
                        q[k2], q[k2 + 1], q[k2 + 2], q[k2 + 3])
                    if d < 0.5 then v = v + 30 + (0.5 - d) end
                end
            end
        end
        local L = lbl_pos[j]
        if not L and j ~= i and ax3 and G.edges[j].label ~= "" then
            L = {x = ax3, y = ay3,
                 w = (A.text_width
                      and A.text_width(G.edges[j].label, -1))
                     or #G.edges[j].label * 5}
        end
        if L and j ~= i then
            local d = geo.rect_rect_dist(lx - tw * 0.5, ly - fh * 0.5,
                tw, fh, L.x - L.w * 0.5, L.y - fh * 0.5, L.w, fh)
            if d < 0.5 then v = v + 25 + (0.5 - d) end
        end
    end
    return v
end

-- label candidate search: each anchor carries its own outward
-- normal, so candidates at u=0.3/0.7 slide ALONG a curve, not just
-- along the apex normal; pushed to both sides at growing offsets,
-- cheapest legal site wins, mild penalties keep the canonical
-- outside anchor when scores tie
local function pick_label(i, bx, by, vox, voy, fh, tw,
                          anchs, off0)
    local bestv, bx2, by2 = math.huge, nil, nil
    for ai2, A2 in ipairs(anchs) do
        local nx2, ny2 = A2.nx, A2.ny
        local o0 = off0 or (2 + tw * 0.5 * math.abs(nx2)
                            + fh * 0.5 * math.abs(ny2))
        for _, s in ipairs{1, -1} do
            for _, d in ipairs{0, 8, 18, 32, 52, 80} do
                local lx2 = A2.x + nx2 * s * (o0 + d)
                local ly2 = A2.y + ny2 * s * (o0 + d)
                local lv = label_viol(i, bx, by, vox, voy,
                                      lx2, ly2, tw, fh)
                local v = lv + d * 0.08 + (s < 0 and 0.6 or 0)
                          + (ai2 - 1) * 0.4
                if v < bestv - 1e-9 then
                    bestv, bx2, by2 = v, lx2, ly2
                end
                -- ideal site free (anchor1/outside/d=0, penalty 0):
                -- nothing can beat v=0 — return without scanning on
                if v <= 0 then return bx2, by2 end
            end
        end
    end
    return bx2, by2
end

-- point at fraction u along a flat polyline (arc length)
local function poly_at(p0, u)
    local total = 0
    for k2 = 1, #p0 - 2, 2 do
        total = total + math.sqrt((p0[k2 + 2] - p0[k2]) ^ 2
                                  + (p0[k2 + 3] - p0[k2 + 1]) ^ 2)
    end
    local want, acc = total * u, 0
    for k2 = 1, #p0 - 2, 2 do
        local l = math.sqrt((p0[k2 + 2] - p0[k2]) ^ 2
                            + (p0[k2 + 3] - p0[k2 + 1]) ^ 2)
        if acc + l >= want and l > 1e-9 then
            local t = (want - acc) / l
            return p0[k2] + (p0[k2 + 2] - p0[k2]) * t,
                   p0[k2 + 1] + (p0[k2 + 3] - p0[k2 + 1]) * t
        end
        acc = acc + l
    end
    return p0[#p0 - 1], p0[#p0]
end

-- unit tangent at fraction u (finite difference of poly_at)
local function poly_dir(p0, u)
    local x1, y1 = poly_at(p0, math.max(0, u - 0.02))
    local x2, y2 = poly_at(p0, math.min(1, u + 0.02))
    local dx, dy = x2 - x1, y2 - y1
    local l = math.sqrt(dx * dx + dy * dy)
    if l < 1e-9 then return 1, 0 end
    return dx / l, dy / l
end

-- point D units of arc length back from the polyline's end
local function poly_back(p0, D)
    local total = 0
    for k = 1, #p0 - 2, 2 do
        total = total + math.sqrt((p0[k + 2] - p0[k]) ^ 2
                                  + (p0[k + 3] - p0[k + 1]) ^ 2)
    end
    return poly_at(p0, math.max(0, (total - D) / math.max(total, 1e-9)))
end

-- unit direction into free space around state `n`: the MAXIMIN
-- direction — the angle whose distance to the NEAREST incident
-- non-loop edge is largest (a flipped mean is meaningless on
-- symmetric neighbourhoods: four orthogonal edges average to ~0 and
-- the fallback then sits the loop/marker right on top of one of them).
-- Second result: the incident-mean direction, or nil when the
-- neighbourhood is symmetric — callers need it for loop-side picks.
local function free_dir(n, def, avoid)
    local dirs, ddx, ddy = {}, 0, 0
    for _, ee in ipairs(G.edges) do
        if ee.from ~= ee.to and (ee.from == n.id or ee.to == n.id) then
            local oi = ee.from == n.id
                     and model.find_state(G, ee.to)
                     or  model.find_state(G, ee.from)
            local o = oi and G.nodes[oi]
            if o then
                local vx, vy = o.x - n.x, o.y - n.y
                local vl = math.sqrt(vx * vx + vy * vy)
                if vl > 1 then
                    dirs[#dirs + 1] = math.atan2(vy, vx)
                    ddx, ddy = ddx + vx / vl, ddy + vy / vl
                end
            end
        end
    end
    local idir = (ddx * ddx + ddy * ddy > 0.2)
                 and math.atan2(ddy, ddx) or nil
    if avoid then
        for _, d in ipairs(avoid) do dirs[#dirs + 1] = d end
    end
    if #dirs == 0 then return def, nil end
    local best, bestscore = def, -1
    for c = 0, 71 do
        local cand = c * math.pi / 36
        local mind = math.pi
        for _, d in ipairs(dirs) do
            local dd = math.abs((cand - d + math.pi)
                                % (2 * math.pi) - math.pi)
            if dd < mind then mind = dd end
        end
        -- slight pull toward `def` breaks ties deterministically
        local score = mind + 0.03 *
            (1 - math.abs((cand - def + math.pi) % (2 * math.pi)
                          - math.pi) / math.pi)
        if score > bestscore then bestscore, best = score, cand end
    end
    return best, idir
end

-- nuklear has no dashed strokes: a dashed segment is a row of short
-- stroke_line dashes (~4 px ink / ~3 px gap).  `c` is an {r,g,b,a}
-- table — col() must stay in tail position at the bridge call, not
-- ride through an intermediate argument
local function dash_line(canvas, x0, y0, x1, y1, w, c)
    local dx, dy = x1 - x0, y1 - y0
    local len = math.sqrt(dx * dx + dy * dy)
    local n = math.max(1, math.floor((len + 3) / 7))
    for i = 0, n - 1 do
        local t0, t1 = i / n, (i + 0.58) / n
        A.stroke_line(canvas, x0 + dx * t0, y0 + dy * t0,
                      x0 + dx * t1, y0 + dy * t1, w, col(c))
    end
end

-- dashed circle for a component's former final state
local function dash_ring(canvas, cx, cy, r, w, c)
    local n = 16
    for i = 0, n - 1 do
        local a0 = (i + 0.16) * 2 * math.pi / n
        local a1 = (i + 0.84) * 2 * math.pi / n
        A.stroke_line(canvas, cx + math.cos(a0) * r,
                      cy + math.sin(a0) * r,
                      cx + math.cos(a1) * r,
                      cy + math.sin(a1) * r, w, col(c))
    end
end

-- free-space score for a label anchor: soft inverse-distance clutter
-- sum over state rims and other transitions' paths — no hard radius,
-- so a merely "less crowded" side (empty margin vs inside a layout)
-- also wins, not just sides that actually collide
local function side_score(px, py, skip, bx, by, vox, voy)
    local s = 0
    for _, n in ipairs(G.nodes) do
        local dx, dy = px - (bx + vox + n.x), py - (by + voy + n.y)
        s = s + 1 / (math.sqrt(dx * dx + dy * dy) - G.NODE_R + 20)
    end
    for j = 1, #G.edges do
        if j ~= skip then
            -- PEEK only — like label_viol: an UNGUARDED call here
            -- would fully RESOLVE every sibling in plain index order
            -- (geo_only still runs the dodge scan + stores
            -- route_res), pre-empting resolve_all's families-first
            -- pass ordering — a single could then lock a route
            -- against a family member's phantom base geometry
            local wc = in_clear
            in_clear = true
            local p2 = aut.edge_poly(j, bx, by, vox, voy, nil, true)
            in_clear = wc
            p2 = route_res[j] or p2
            if p2 then
                s = s + 2 / (geo.poly_dist(p2, px, py) + 20)
            end
        end
    end
    return s
end

function aut.edge_poly(i, bx, by, vox, voy, fh, geo_only)
    fh = fh or 14
    local e = G.edges[i]
    if not e then return nil end
    if not geo_only then
        if G.dragging then
            drag_was = true
        elseif drag_was then
            -- drag released: the thin-scan routes were approximate —
            -- drop the whole scene so this frame re-resolves with the
            -- full candidate set, labels and the fixpoint pass
            drag_was, lbl_sig = false, nil
            drag_settle = true
        end
        local sig = scene_sig(bx, by, vox, voy, fh)
        if sig ~= lbl_sig then
            local ps = prev_scene
            -- a released drag must go through the FULL wipe below:
            -- prev_scene tracked the last drag frame, so the scoped
            -- diff sees "nothing moved" and would carry every
            -- approximate route over verbatim
            local sameview = not drag_settle
                and ps and ps.bx == bx and ps.by == by
                and ps.vox == vox and ps.voy == voy and ps.fh == fh
            drag_settle = false
            if sameview then
                -- scoped invalidation: an edge re-resolves only if
                -- it changed itself or something moved inside its
                -- candidate reach; every other cached route is
                -- provably identical and carries over by edge id
                local changed, seed = {}, {}
                local NP = G.NODE_R + 10
                local function nbox(x, y)
                    changed[#changed + 1] =
                        {bx + vox + x - NP, by + voy + y - NP,
                         bx + vox + x + NP, by + voy + y + NP}
                end
                local nnow = {}
                for _, n in ipairs(G.nodes) do
                    nnow[n.id] = n
                    local p = ps.nodes[n.id]
                    if not p or p.x ~= n.x or p.y ~= n.y then
                        nbox(n.x, n.y)
                        if p then nbox(p.x, p.y) end
                    end
                end
                for id, p in pairs(ps.nodes) do
                    if not nnow[id] then nbox(p.x, p.y) end
                end
                local new_res, new_bb, new_lbl, kept = {}, {}, {}, {}
                local enow = {}
                for j, e in ipairs(G.edges) do enow[e.id] = j end
                -- endpoint pairs whose sibling group changed: an
                -- added/removed/rewired edge reclassifies every
                -- sibling between the same states (single <-> fan
                -- <-> bidirectional) — a STRUCTURAL trigger the
                -- geometric reach rule cannot see
                local touched, touched_nodes = {}, {}
                local function touch(a, b)
                    touched[a .. ">" .. b] = true
                    -- node-level record for self-loops: a loop's
                    -- free_dir depends on EVERY incident non-loop
                    -- edge, so a (from,to) pair change on either
                    -- endpoint must dirty it too — the pair key
                    -- "q0>q0" alone misses that
                    touched_nodes[a] = true
                    touched_nodes[b] = true
                end
                for _, e in ipairs(G.edges) do
                    local pe = ps.edges[e.id]
                    if not pe then
                        touch(e.from, e.to)
                    elseif pe.from ~= e.from or pe.to ~= e.to then
                        touch(pe.from, pe.to)
                        touch(e.from, e.to)
                    end
                end
                for id, pe in pairs(ps.edges) do
                    if not enow[id] then touch(pe.from, pe.to) end
                end
                for j, e in ipairs(G.edges) do
                    local pe = ps.edges[e.id]
                    local oj = pe and pe.j
                    local rewired = not pe or pe.from ~= e.from
                        or pe.to ~= e.to
                    local relabeled = pe and (pe.label or "")
                        ~= (e.label or "")
                    local dirty = rewired
                        or touched[e.from .. ">" .. e.to]
                        or touched[e.to .. ">" .. e.from]
                        or (e.from == e.to and touched_nodes[e.from])
                    if not dirty then
                        local r = edge_reach(j, bx, by, vox, voy)
                        for _, cb in ipairs(changed) do
                            if rect_bb_dist(r[1], r[2], r[3], r[4], cb)
                                    <= 9 then
                                dirty = true
                                break
                            end
                        end
                    end
                    if relabeled and not dirty then
                        -- route geometry does not depend on the
                        -- label text — carry it, re-place the label
                        new_res[j], new_bb[j] =
                            route_res[oj], route_bb[oj]
                    elseif dirty then
                        -- keep_route is only a valid candidate when
                        -- the cached poly still CONNECTS this edge's
                        -- endpoints.  A moved endpoint invalidates
                        -- it: scored in the new scene it lands in
                        -- empty space and wins hysteresis while its
                        -- tip/tail point nowhere.
                        local n1, n2 = nnow[e.from], nnow[e.to]
                        local p1 = pe and ps.nodes[e.from]
                        local p2 = pe and ps.nodes[e.to]
                        local epmoved = rewired or not p1 or not p2
                            or p1.x ~= n1.x or p1.y ~= n1.y
                            or p2.x ~= n2.x or p2.y ~= n2.y
                        if epmoved or not oj then
                            -- old corridor frees up; treat as fresh
                            -- geometry — no hysteresis
                            if oj and route_bb[oj] then
                                seed[#seed + 1] = route_bb[oj]
                            end
                        elseif route_res[oj] then
                            kept[j] = {poly = route_res[oj],
                                       bb = route_bb[oj]}
                        end
                    else
                        new_res[j], new_bb[j], new_lbl[j] =
                            route_res[oj], route_bb[oj], lbl_pos[oj]
                    end
                end
                for id, pe in pairs(ps.edges) do
                    if not enow[id] and route_bb[pe.j] then
                        seed[#seed + 1] = route_bb[pe.j]
                    end
                end
                for _, cb in ipairs(changed) do
                    seed[#seed + 1] = cb
                end
                -- seeds ACCUMULATE across wipes before the next
                -- resolve — a second edit must not lose the first
                -- edit's freed/moved regions
                if fp_seed then
                    for _, s in ipairs(seed) do
                        fp_seed[#fp_seed + 1] = s
                    end
                else
                    fp_seed = seed
                end
                kept_hyst = kept
                lbl_sig, lbl_pos, route_res, route_bb =
                    sig, new_lbl, new_res, new_bb
            else
                -- first scene or the view transform moved: nothing
                -- carries over (routes are view-space geometry)
                lbl_sig, lbl_pos, route_res, route_bb = sig, {}, {}, {}
                fp_seed, kept_hyst = nil, nil
            end
            prev_scene = {bx = bx, by = by, vox = vox, voy = voy,
                          fh = fh, nodes = {}, edges = {}}
            for _, n in ipairs(G.nodes) do
                prev_scene.nodes[n.id] = {x = n.x, y = n.y}
            end
            for j, e in ipairs(G.edges) do
                prev_scene.edges[e.id] =
                    {from = e.from, to = e.to, label = e.label, j = j}
            end
            refined = false
        end
    end
    if route_res[i] then
        -- resolved earlier in this scene: the geometry is fixed;
        -- only the label search may still be pending
        local pts0 = route_res[i]
        local L = lbl_pos[i]
        if geo_only or (e.label or "") == "" or L then
            return pts0, L and L.x or pts0._ax,
                         L and L.y or pts0._ay
        end
        -- while a state is dragged the scene changes every frame:
        -- routes re-resolve (needed for live feedback) but the label
        -- candidate scan is deferred — the anchor follows the route
        -- and the real placement runs once on the settle frame
        if G.dragging then
            return pts0, pts0._ax, pts0._ay
        end
        -- two-phase placement: every route must be resolved before
        -- the first label is placed — label_viol needs each sibling's
        -- REAL arc, otherwise a label dodges a base route the sibling
        -- never took and ends up on its resolved arc
        resolve_all(bx, by, vox, voy, fh)
        pts0 = route_res[i]
        local tw = (A.text_width and A.text_width(e.label, -1))
                   or #e.label * 5
        local anchs = {{x = pts0._ax, y = pts0._ay,
                        nx = pts0._nx, ny = pts0._ny}}
        for _, u in ipairs{0.3, 0.7} do
            local ux2, uy2 = poly_at(pts0, u)
            local tdx, tdy = poly_dir(pts0, u)
            anchs[#anchs + 1] = {x = ux2, y = uy2,
                                 nx = -tdy, ny = tdx}
        end
        local lx2, ly2 = pick_label(i, bx, by, vox, voy, fh, tw, anchs)
        lbl_pos[i] = {x = lx2, y = ly2, w = tw, h = fh}
        return pts0, lx2, ly2
    end
    local ai, bi = model.find_state(G, e.from), model.find_state(G, e.to)
    if not (ai and bi) then return nil end
    local a, b = G.nodes[ai], G.nodes[bi]
    local ax, ay = bx + vox + a.x, by + voy + a.y
    local tx, ty = bx + vox + b.x, by + voy + b.y
    if ai == bi then
        -- self-loop(s): a true circular arc meeting the rim at dir±psi.
        -- The loop faces away from the state's incident edges (mean
        -- direction flipped) instead of a fixed "up" — on a square it
        -- points outward, not into the neighbouring edges
        local k, nf = edge_siblings(i)
        -- the initial marker occupies its own sector: fold its
        -- direction into the maximin obstacles so the loop picks a
        -- genuinely free cone instead of getting folded sideways into
        -- an edge corridor by a post-hoc nudge
        local dir, idir
        if a.initial then
            dir, idir = free_dir(a, -math.pi * 0.5,
                                 {free_dir(a, math.pi)})
        else
            dir, idir = free_dir(a, -math.pi * 0.5)
        end
        dir = dir + (k - (nf + 1) / 2) * 1.12
        local pts, apx, apy =
            geo.loop_arc({}, ax, ay, G.NODE_R, dir)
        local lx, ly = apx + math.cos(dir) * LBL_OFF,
                       apy + math.sin(dir) * LBL_OFF
        if not geo_only and e.label ~= "" and not G.dragging then
            -- loop labels get their own candidate fan: the apex plus
            -- ±35°/±70° siblings around the same node, each pushed
            -- along its own radial normal
            local tw = (A.text_width and A.text_width(e.label, -1))
                       or #e.label * 5
            local anchs = {{x = apx, y = apy,
                            nx = math.cos(dir), ny = math.sin(dir)}}
            for _, da in ipairs{0.6, 1.2} do
                anchs[#anchs + 1] = {
                    x = ax + math.cos(dir + da) * (2.3 * G.NODE_R),
                    y = ay + math.sin(dir + da) * (2.3 * G.NODE_R),
                    nx = math.cos(dir + da), ny = math.sin(dir + da)}
                anchs[#anchs + 1] = {
                    x = ax + math.cos(dir - da) * (2.3 * G.NODE_R),
                    y = ay + math.sin(dir - da) * (2.3 * G.NODE_R),
                    nx = math.cos(dir - da), ny = math.sin(dir - da)}
            end
            lx, ly = pick_label(i, bx, by, vox, voy, fh, tw,
                                anchs, LBL_OFF + 2)
        end
        if not in_clear then
            pts._ax, pts._ay = apx, apy
            pts._nx, pts._ny = math.cos(dir), math.sin(dir)
            route_res[i], route_bb[i] = pts, poly_bb(pts)
            if not geo_only then
                lbl_pos[i] = {x = lx, y = ly,
                              w = (A.text_width
                                   and A.text_width(e.label, -1))
                                  or #e.label * 5,
                              h = fh}
            end
        end
        return pts, lx, ly
    end
    local k, nf, nr, br = edge_siblings(i)
    -- CENTRE-to-CENTRE curves clipped at the state rims: what the
    -- student sees is the part of a centre-pointing curve that lies
    -- outside both discs, so arrowheads always land radial to the
    -- target centre.  Families fan by arc DEPTH (deeper shell per
    -- rank), not by attach angle.
    local dx, dy = tx - ax, ty - ay
    local dl = math.sqrt(dx * dx + dy * dy)
    local ux, uy = dx / dl, dy / dl

    -- deterministic bow side: away from the mass of the other states
    -- (a node ON the chord pulls ~0), tie → +h side.  Same for
    -- hit-testing and drawing; the clearance search may still flip
    -- when the preferred side stays obstructed.
    local mass = 0
    for j, n in ipairs(G.nodes) do
        if j ~= ai and j ~= bi then
            local rx = bx + vox + n.x - ax
            local ry = by + voy + n.y - ay
            local perp = rx * (-dy) + ry * dx
            mass = mass + perp / (math.abs(perp) + 0.02 * dl + 40)
        end
    end
    local defside = mass > 0 and -1 or 1

    local h = 0
    if nr > 0 then
        -- bidirectional family: each direction bows to its OWN side —
        -- the classic symmetric lens, a deeper shell per same-
        -- direction rank.  ONE family sign, decided on the canonical
        -- chord (from<to): mass>0 pushes the canonical direction to
        -- -n, otherwise +n; reverse members mirror it automatically
        -- because their own normal flips (a shared sign = opposite
        -- geometric sides)
        local sfam
        if e.from < e.to then
            sfam = mass > 0 and -1 or 1
        else
            sfam = mass < 0 and -1 or 1
        end
        h = sfam * dl * (0.16 + 0.13 * (k - 1))
    elseif nf > 1 then
        -- same-direction lens: sides alternate, depth grows per pair
        h = (k % 2 == 1 and 1 or -1) * dl * (0.10 + 0.10 * math.ceil(k / 2))
    else
        -- single edge: straight unless the chord tunnels a third
        -- state — bow away from the blocker (or the node mass for a
        -- centred blocker), deep enough to clear its rim at the
        -- projection point (arc height at u ≈ 4·h·u(1-u)).  Shell
        -- ordering: an edge whose span CONTAINS a sibling dodge's
        -- span owns the outer shell and bows deeper
        local shell = 0
        for j, ej in ipairs(G.edges) do
            if j ~= i and ej.from ~= ej.to
               and (ej.from == e.from or ej.from == e.to
                    or ej.to == e.from or ej.to == e.to) then
                local k2, nf2 = edge_siblings(j)
                if nf2 == 1 then
                    local aj = model.find_state(G, ej.from)
                    local bj = model.find_state(G, ej.to)
                    if aj and bj then
                        local t1 = (bx + vox + G.nodes[aj].x - ax) * ux
                                 + (by + voy + G.nodes[aj].y - ay) * uy
                        local t2 = (bx + vox + G.nodes[bj].x - ax) * ux
                                 + (by + voy + G.nodes[bj].y - ay) * uy
                        local lo, hi = math.min(t1, t2),
                                       math.max(t1, t2)
                        if lo > -8 and hi < dl + 8 then
                            shell = shell + 1
                        end
                    end
                end
            end
        end
        for j, n in ipairs(G.nodes) do
            if j ~= ai and j ~= bi then
                local rx = bx + vox + n.x - ax
                local ry = by + voy + n.y - ay
                local u = (rx * ux + ry * uy) / dl
                if u > 0.04 and u < 0.96 then
                    local perp = rx * (-uy) + ry * ux
                    local need = (G.NODE_R + 16) - math.abs(perp)
                    if need > 0 then
                        local s = need / (4 * u * (1 - u))
                        if s > math.abs(h) then
                            local side = perp >= G.NODE_R * 0.6 and -1
                                       or perp <= -G.NODE_R * 0.6 and 1
                                       or defside
                            h = side * s
                        end
                    end
                end
            end
        end
        if h ~= 0 and shell > 0 then
            h = (h >= 0 and 1 or -1) * (math.abs(h) + shell * 26)
        end
    end

    -- proper intersection point of two segments, or nil
    local function seg_xing(ax2, ay2, bx2, by2, cx2, cy2, dx2, dy2)
        local rx2, ry2 = bx2 - ax2, by2 - ay2
        local sx2, sy2 = dx2 - cx2, dy2 - cy2
        local d = rx2 * sy2 - ry2 * sx2
        if math.abs(d) < 1e-9 then return nil end
        local t = ((cx2 - ax2) * sy2 - (cy2 - ay2) * sx2) / d
        local u = ((cx2 - ax2) * ry2 - (cy2 - ay2) * rx2) / d
        if t <= 1e-6 or t >= 1 - 1e-6 or u <= 1e-6 or u >= 1 - 1e-6 then
            return nil
        end
        return ax2 + rx2 * t, ay2 + ry2 * t
    end

    -- clip a centre-to-centre polyline to the part outside both state
    -- discs: the stroke keeps the LAST exit crossing of the source
    -- disc and the FIRST entry crossing of the target disc (a deep
    -- arc could otherwise re-enter a disc it already left)
    local function clip_rims(p0)
        local R2 = G.NODE_R * G.NODE_R
        local n = #p0 / 2
        local function inside(k, cx, cy)
            local ddx2, ddy2 = p0[2 * k - 1] - cx, p0[2 * k] - cy
            return ddx2 * ddx2 + ddy2 * ddy2 < R2
        end
        -- segment-circle crossing, fraction t along (k1 -> k2)
        local function xfrac(k1, k2, cx, cy)
            local px2, py2 = p0[2*k1-1] - cx, p0[2*k1] - cy
            local dx2 = p0[2*k2-1] - p0[2*k1-1]
            local dy2 = p0[2*k2]   - p0[2*k1]
            local a2 = dx2 * dx2 + dy2 * dy2
            if a2 < 1e-9 then return nil end
            local b2 = 2 * (px2 * dx2 + py2 * dy2)
            local c2 = px2 * px2 + py2 * py2 - R2
            local disc = b2 * b2 - 4 * a2 * c2
            if disc < 0 then return nil end
            local sq = math.sqrt(disc)
            for _, t in ipairs{(-b2 + sq) / (2 * a2),
                               (-b2 - sq) / (2 * a2)} do
                if t >= 0 and t <= 1 then return t end
            end
            return nil
        end
        -- last vertex inside the source disc → cut on (si, si+1)
        local si = 0
        for k2 = 1, n do if inside(k2, ax, ay) then si = k2 end end
        -- first vertex inside the target disc (from the back) →
        -- cut on (ei-1, ei)
        local ei = n + 1
        for k2 = n, 1, -1 do if inside(k2, tx, ty) then ei = k2 end end
        if si >= ei then return nil end   -- discs swallow all
        local out = {}
        local t = xfrac(si, si + 1, ax, ay)
        out[#out + 1] = p0[2*si-1] + (p0[2*si+1] - p0[2*si-1]) * (t or 1)
        out[#out + 1] = p0[2*si]   + (p0[2*si+2] - p0[2*si])   * (t or 1)
        for k2 = si + 1, ei - 1 do
            out[#out + 1] = p0[2*k2-1]
            out[#out + 1] = p0[2*k2]
        end
        t = xfrac(ei - 1, ei, tx, ty)
        out[#out + 1] = p0[2*ei-3] + (p0[2*ei-1] - p0[2*ei-3]) * (t or 0)
        out[#out + 1] = p0[2*ei-2] + (p0[2*ei]   - p0[2*ei-2]) * (t or 0)
        return out
    end

    -- arc candidate through both CENTRES, clipped at the rims;
    -- nseg<nil coarsens the tessellation for cheap candidate scoring
    local function build_arc(hh, nseg)
        local p0, apx2, apy2, nl2x, nl2y =
            geo.arc_poly({}, ax, ay, tx, ty, hh, nseg)
        local cl = clip_rims(p0)
        if not cl then
            -- degenerate (overlapping discs): straight rim points
            cl = {ax + ux * G.NODE_R, ay + uy * G.NODE_R,
                  tx - ux * G.NODE_R, ty - uy * G.NODE_R}
        end
        return cl, apx2, apy2, nl2x, nl2y
    end

    -- flat-top "wire" candidate: cubic through both centres, control
    -- feet at 18%/82% of the chord raised to hh/0.75 so the plateau
    -- tops out at hh — steep legs leaving the states, a level cruise
    -- between them (the "up a bit, then across" shape)
    local function build_bez(hh, nseg)
        local hgt = hh / 0.75
        local x1 = ax + ux * dl * 0.18 - uy * hgt
        local y1 = ay + uy * dl * 0.18 + ux * hgt
        local x2 = ax + ux * dl * 0.82 - uy * hgt
        local y2 = ay + uy * dl * 0.82 + ux * hgt
        local p0 = geo.bez3({}, ax, ay, x1, y1, x2, y2, tx, ty,
                            nseg or 32)
        local cl = clip_rims(p0)
        if not cl then
            cl = {ax + ux * G.NODE_R, ay + uy * G.NODE_R,
                  tx - ux * G.NODE_R, ty - uy * G.NODE_R}
        end
        local s = hh >= 0 and 1 or -1
        return cl, (ax + tx) * 0.5 - uy * hh,
                   (ay + ty) * 0.5 + ux * hh, -uy * s, ux * s
    end

    -- (nf alone does NOT mean single — a bidirectional member has
    -- nf=1 too; it needs nr==0 as well)
    local single = nr == 0 and nf <= 1
    local pts, apx, apy, nlx, nly
    if not in_clear and (h ~= 0 or single) then
        -- BOUNDED candidate search instead of blind sagitta growth:
        -- deepening a circular arc past ~90° wraps it around the whole
        -- neighbourhood (major arc), and deepening into a sibling's
        -- corridor CROSSES it — neither is found by "grow until clear".
        -- Every candidate is scored by violation count; the preferred
        -- side is tried shallow→deep first, the flip side only when
        -- that stays obstructed.  in_clear makes nested edge_poly
        -- calls (foreign geometry snapshot) return base geometry, so
        -- hit-testing (geo_only) resolves the same route as drawing.
        in_clear = true
        local fpoly = {}
        local fbb = {}
        local fres = {}   -- snapshots that are RESOLVED routes
        for j = 1, #G.edges do
            if j ~= i then
                fres[j] = route_res[j] ~= nil
                -- prefer the route this edge already RESOLVED to in
                -- this scene (label placement + drawing see the same
                -- polylines); fall back to base geometry for edges
                -- not yet routed.  Family members count too: a
                -- flipped candidate must not collapse onto a
                -- sibling's arc (rim-exempt zones cover their
                -- legitimate convergence)
                fpoly[j] = route_res[j]
                        or aut.edge_poly(j, bx, by, vox, voy,
                                         nil, true)
                fbb[j] = route_res[j] and route_bb[j]
                         or poly_bb(fpoly[j])
            end
        end
        local exr = G.NODE_R + 18
        local exr2 = exr * exr
        local last_vb
        local function viol(p0)
            local v = 0
            local vb = DBG_EDGE == i and {} or nil
            last_vb = vb
            local function add(tag, w)
                v = v + w
                if vb then vb[tag] = (vb[tag] or 0) + w end
            end
            local pbb = poly_bb(p0)
            local nr = G.NODE_R + 4
            -- a wire must not fold back onto itself IN FREE SPACE:
            -- a via/pocket that wraps a blocker legitimately hugs its
            -- rim (approach midpoint near a node = designed wrap),
            -- but doubling back within a few px of its own approach
            -- corridor with nothing between draws a pointless
            -- Schleife.  Loops exempt — their teardrop neck is
            -- designed proximity
            if e.from ~= e.to then
                local np2 = #p0
                local wrapr = G.NODE_R + 10
                -- along-wire distance between segment starts: dense
                -- polylines have ~4px segments, so adjacency must be
                -- skipped by ARC LENGTH, not index
                local cum = {}
                cum[1] = 0
                for k = 1, np2 - 2, 2 do
                    cum[k + 2] = cum[k] + math.sqrt(
                        (p0[k + 2] - p0[k]) ^ 2
                        + (p0[k + 3] - p0[k + 1]) ^ 2)
                end
                for a2 = 1, np2 - 6, 2 do
                    for b2 = a2 + 4, np2 - 2, 2 do
                        if cum[b2] - cum[a2] > 40 then
                        local d = math.min(
                            geo.pt_seg_dist(p0[a2], p0[a2 + 1],
                                p0[b2], p0[b2 + 1],
                                p0[b2 + 2], p0[b2 + 3]),
                            geo.pt_seg_dist(p0[a2 + 2], p0[a2 + 3],
                                p0[b2], p0[b2 + 1],
                                p0[b2 + 2], p0[b2 + 3]),
                            geo.pt_seg_dist(p0[b2], p0[b2 + 1],
                                p0[a2], p0[a2 + 1],
                                p0[a2 + 2], p0[a2 + 3]),
                            geo.pt_seg_dist(p0[b2 + 2], p0[b2 + 3],
                                p0[a2], p0[a2 + 1],
                                p0[a2 + 2], p0[a2 + 3]))
                        if d < 10 then
                            -- approach midpoint inside a node's rim
                            -- zone = the wire wraps that blocker,
                            -- not free space
                            local mx = (p0[a2] + p0[a2 + 2]
                                        + p0[b2] + p0[b2 + 2]) / 4
                            local my = (p0[a2 + 1] + p0[a2 + 3]
                                        + p0[b2 + 1] + p0[b2 + 3]) / 4
                            local wrapped = false
                            for _, n in ipairs(G.nodes) do
                                local nx3 = bx + vox + n.x
                                local ny3 = by + voy + n.y
                                if (mx - nx3) * (mx - nx3)
                                   + (my - ny3) * (my - ny3)
                                   < wrapr * wrapr then
                                    wrapped = true; break
                                end
                            end
                            if not wrapped then
                                add('self', (10 - d) * 8)
                            end
                        end
                        end
                    end
                end
            end
            for j, n in ipairs(G.nodes) do
                if j ~= ai and j ~= bi then
                    local nx2, ny2 = bx + vox + n.x, by + voy + n.y
                    -- a node outside the candidate's inflated bbox
                    -- cannot touch any of its segments
                    if nx2 >= pbb[1] - nr and nx2 <= pbb[3] + nr
                       and ny2 >= pbb[2] - nr
                       and ny2 <= pbb[4] + nr then
                        for k2 = 1, #p0 - 2, 2 do
                            if geo.pt_seg_dist(nx2, ny2, p0[k2],
                                p0[k2 + 1], p0[k2 + 2], p0[k2 + 3])
                                < nr then
                                add('node' .. j, 500); break
                            end
                        end
                    end
                end
            end
            for j, q in pairs(fpoly) do
                local ej = G.edges[j]
                -- rim slots on a shared node: an arrowhead — flared
                -- and wide — must keep ~20px clear of another head
                -- or a bare tail; only TAILS may sit tighter (they
                -- diverge at once, and the chord's owner is exempt —
                -- see below)
                local function rimchk(x1, y1, x2, y2, margin)
                    local dd = math.sqrt((x1 - x2) ^ 2 + (y1 - y2) ^ 2)
                    if dd < margin then
                        add('rim' .. j, (margin - dd) * 2)
                    end
                end
                -- rim slots only against RESOLVED routes: an
                -- unresolved sibling's BASE tip is not where its
                -- arrowhead will land (dodging a phantom slot used
                -- to push siblings off their designed side)
                if ej.to == e.to and fres[j] then
                    rimchk(p0[#p0 - 1], p0[#p0], q[#q - 1], q[#q], 20)
                end
                if ej.from == e.from and fres[j] then
                    -- tails are thin and diverge at once: only a
                    -- DISPLACED departure may not crowd a sibling's
                    -- tail.  The slot's owner — a route leaving on
                    -- its own chord crossing — can never be the
                    -- intruder (q1->q5 used to bow over free space
                    -- only because q1->q6's dodge parked its tail
                    -- on the shared chord slot)
                    local dd = math.sqrt(
                        (p0[1] - q[1]) ^ 2 + (p0[2] - q[2]) ^ 2)
                    if dd < 10 then
                        local cd = math.sqrt(
                            (p0[1] - (ax + ux * G.NODE_R)) ^ 2
                          + (p0[2] - (ay + uy * G.NODE_R)) ^ 2)
                        if cd > 4 then
                            add('rim' .. j, (10 - dd) * 2)
                        end
                    end
                end
                -- and head-into-tail on the shared rim: our landing
                -- must not crowd an edge LEAVING the node we enter
                -- (or its landing crowd our departure).  The true
                -- reverse sibling is exempt: a lens is DESIGNED to
                -- converge head-into-tail at its tips
                local rev = ej.from == e.to and ej.to == e.from
                if ej.from == e.to and not rev and fres[j] then
                    rimchk(p0[#p0 - 1], p0[#p0], q[1], q[2], 20)
                end
                if ej.to == e.from and not rev and fres[j] then
                    rimchk(p0[1], p0[2], q[#q - 1], q[#q], 20)
                end
                -- near-misses outside our rim zones — and the
                -- crossing scan below: both impossible when the
                -- polylines' bboxes sit further apart than the
                -- near-miss margin (crossings need overlap)
                if rect_bb_dist(pbb[1], pbb[2], pbb[3], pbb[4],
                                fbb[j]) <= 9 then
                for k2 = 1, #p0, 2 do
                    local x, y = p0[k2], p0[k2 + 1]
                    local da = (x - ax) * (x - ax) + (y - ay) * (y - ay)
                    local db = (x - tx) * (x - tx) + (y - ty) * (y - ty)
                    if da > exr2 and db > exr2 then
                        local d = geo.poly_dist(q, x, y)
                        if d < 9 then add('near' .. j, 9 - d) end
                    end
                end
                -- real crossings count heavier than near-misses —
                -- and a crossing with an edge that shares one of our
                -- endpoints is much worse than an unrelated mid-air
                -- crossing (that one is a layout problem, ours is a
                -- routing bug).  Exempt ONLY crossings hard against
                -- the rim itself — the unavoidable tip-order swap
                -- happens inside an arrowhead's length of the rim;
                -- everything further out is approach interference
                -- (a detour slicing through a node's whole arrival
                -- fan at ~30px LOOKED clean and won: q6->q3 diving
                -- through a bidirectional lens).  Same radius loops
                -- already had — their wire wraps far
                local loopj = ej.from == ej.to
                local er2 = G.NODE_R + 2
                er2 = er2 * er2
                local shared = (ej.from == e.from or ej.from == e.to
                                or ej.to == e.from or ej.to == e.to)
                -- a FAMILY member crossing anything is a routing
                -- failure, not a layout problem: its designed place
                -- is inside the fan, so prefer rim crowding over an
                -- unrelated mid-air crossing.  Singles pay more than
                -- they used to, too: when every legal landing crowds
                -- a shared rim the scorer must still prefer
                -- crowded-but-correct over a crossing — 15 let a
                -- crossing detour beat a 60pt rim squeeze (q6->q3
                -- threading under a lens vs. sweeping over the top)
                local xcost = (shared or not single) and 150 or 60
                for a2 = 1, #p0 - 2, 2 do
                    for b2 = 1, #q - 2, 2 do
                        local x, y = seg_xing(p0[a2], p0[a2 + 1],
                            p0[a2 + 2], p0[a2 + 3],
                            q[b2], q[b2 + 1], q[b2 + 2], q[b2 + 3])
                        if x then
                            local ok = false
                            if ej.from == e.from or ej.to == e.from then
                                ok = (x - ax)^2 + (y - ay)^2 < er2
                            end
                            if not ok and (ej.from == e.to
                                           or ej.to == e.to) then
                                ok = (x - tx)^2 + (y - ty)^2 < er2
                            end
                            if not ok then
                                add((shared and 'xs' or 'xu') .. j,
                                    xcost)
                            end
                        end
                    end
                end
                end
            end
            return v
        end

        -- a single whose chord is node-free reaches here with h==0:
        -- the one reason left to bow is a FOREIGN ROUTE — the
        -- straight chord may still cross or hug another transition's
        -- resolved line.  Score it like any candidate; only a dirty
        -- chord seeds the dodge scan (with a shallow baseline — the
        -- ladder's 0-entry keeps the chord itself in the running, so
        -- an unavoidable crossing stays straight instead of bowing
        -- into something worse)
        if h == 0 and viol(build_arc(0, 24)) > 0 then
            h = defside * dl * 0.16
        end

        local pref = h >= 0 and 1 or -1
        local best, clean = nil, false
        local clean_best   -- shallowest CLEAN route across both sides
        -- depth ladder: the designed depth first, then SHALLOWER
        -- (slip into the wedge between own chord and a foreign edge)
        -- then deeper shells; the cap keeps arcs below ~90° so a
        -- candidate never wraps around a whole neighbourhood
        -- TRUE singles scan SHALLOW-first: their designed depth
        -- carries a shell surcharge for contained spans, but the
        -- minimal bow that clears the blocker takes the least space.
        -- The leading 0 keeps the straight chord as an explicit
        -- fallback candidate.  Families keep depth-first: their bow
        -- is the designed lens spacing, shrinking it would collapse
        -- the fan
        local ladder
        if G.dragging then
            -- drag frames only need an approximate route: designed
            -- depth + straight/deep fallback; the settle frame
            -- re-resolves with the full ladder
            ladder = single and {0, 1, 3.0} or {1, 2.1}
        else
            ladder = single and {0, 0.25, 0.5, 1, 1.45, 2.1, 3.0}
                            or {1, 0.5, 0.25, 1.15, 1.45, 1.75,
                                2.1, 3.0}
        end
        -- long singles also try flat-top bezier "wire" routes —
        -- the wire wins ties over the arc (its plateau hugs the
        -- corridor instead of sweeping a half-circle)
        local kinds = (single and dl > 160) and {"arc", "bez"}
                                          or  {"arc"}
        -- route footprint: max perpendicular offset from the chord —
        -- the tie-break between equally-clean candidates (a flat wire
        -- beats a deep arc covering the same ground)
        local function poly_dev(p0)
            local d = 0
            for k = 1, #p0, 2 do
                local pd = math.abs((p0[k] - ax) * (-uy)
                                  + (p0[k + 1] - ay) * ux)
                if pd > d then d = pd end
            end
            return d
        end
        local function scan(sgn)
            local h0 = math.abs(h)
            for _, f in ipairs(ladder) do
                local hh = h0 * f
                if hh <= dl * 0.55 then
                    local clean = false
                    for _, kind in ipairs(kinds) do
                        local bld = kind == "bez" and build_bez
                                                 or  build_arc
                        local p0 = bld(sgn * hh, 24)
                        local v = viol(p0)
                        if kind == "bez" then v = v - 0.5 end
                        if DBG_EDGE == i then
                            local tags = {}
                            for t2, w2 in pairs(last_vb or {}) do
                                tags[#tags + 1] = string.format(
                                    '%s=%s', t2, tostring(w2))
                            end
                            table.sort(tags)
                            print(string.format(
                                "  e%d cand s=%d %s h=%.0f viol=%.1f  %s",
                                i, sgn, kind, hh, v,
                                table.concat(tags, ' ')))
                        end
                        if not best or v < best.v - 0.5
                           or (math.abs(v - best.v) <= 0.5
                               and poly_dev(p0) + 1
                                   < poly_dev(best._poly or best.via)) then
                            best = {v = v, hh = sgn * hh,
                                    kind = kind, _poly = p0}
                        end
                        if v <= 0 then
                            clean = true
                            if not clean_best or math.abs(hh)
                               < math.abs(clean_best.hh) then
                                clean_best = {v = v, hh = sgn * hh,
                                              kind = kind}
                            end
                        end
                    end
                    if clean then return true end
                end
            end
            return false
        end
        clean = scan(pref)
        -- flip is the LAST RESORT, not banned — a fully obstructed
        -- designed side (node disc, self-loop cone) may still force
        -- it.  BUT a family member must never land on a side a
        -- reverse sibling already occupies: that is the collapsed
        -- "both arrows hug one side" look.  Detect that from the
        -- sibling's route midpoint signed to OUR chord normal and
        -- skip the flip entirely
        local flip_ok = true
        if not single then
            for j, ej in ipairs(G.edges) do
                if ej.from == e.to and ej.to == e.from then
                    local q = route_res[j]
                           or aut.edge_poly(j, bx, by, vox, voy,
                                            nil, true)
                    if q then
                        local mi = (math.floor(#q / 4) or 1) * 2 - 1
                        local perp = (q[mi] - ax) * (-uy)
                                   + (q[mi + 1] - ay) * ux
                        -- a sibling on the flip side bans the flip
                        -- only when it hugs SHALLOW — a deep sibling
                        -- shell leaves the corridor inside free, and
                        -- a nested detour arc beats a crossing
                        if perp * pref < 0
                           and math.abs(perp) < dl * 0.22 then
                            flip_ok = false
                            break
                        end
                    end
                end
            end
        end
        local flip_scanned = false
        if not clean and flip_ok then
            clean = scan(-pref)
            flip_scanned = true
        end
        -- ...but a single whose preferred side only clears DEEP (or
        -- not at all) also tries the flip side: a shallow route around
        -- the obstacle side reads better than a huge sweep through
        -- free space.  And when even that leaves only a deep sweep —
        -- or nothing — explicit waypoint routes ("mehrere
        -- Haltepunkte") hugging the corridor blockers get a try: a
        -- quadratic through one rim-pocket, a cubic through two, with
        -- the controls interpolated so the curve passes THROUGH the
        -- pocket exactly
        local via_best        -- first CLEAN waypoint/corridor route
        local via_min         -- min-viol via candidate, clean or not
        local arc_best        -- min viol over arc/bez candidates only
        -- "deep" is bounded absolutely AND relatively: a 155px bow on
        -- a 528px chord is only 0.29·dl yet still exits the viewport —
        -- waypoint routes get their try whenever the clean sweep is
        -- deeper than a wire would need
        local deep = math.min(dl * 0.30, 60)
        if single and not flip_scanned
           and (not clean_best or math.abs(clean_best.hh) > deep)
        then
            scan(-pref)
        end
        if single
           and (not clean_best or math.abs(clean_best.hh) > deep)
        then
            -- chord blockers = nodes inside the corridor the straight
            -- line must dodge; corridor nodes sit further out — their
            -- flank IS the detour wall (a bidirectional lens or rim
            -- traffic can make the chord-adjacent wrap the dirty one,
            -- while the only clean door lies BEHIND the next node).
            -- Keep the window wide: pockets/channels are scored by
            -- viol() anyway, a far node's shapes just cost cycles.
            local blockers = {}
            for j, n in ipairs(G.nodes) do
                if j ~= ai and j ~= bi then
                    local rx = bx + vox + n.x - ax
                    local ry = by + voy + n.y - ay
                    local u = (rx * ux + ry * uy) / dl
                    local perp = rx * (-uy) + ry * ux
                    if u > 0.08 and u < 0.92
                       and math.abs(perp) < G.NODE_R + 80 then
                        blockers[#blockers + 1] =
                            {x = bx + vox + n.x, y = by + voy + n.y,
                             u = u, perp = perp}
                    end
                end
            end
            table.sort(blockers, function(p, q)
                return math.abs(p.perp) < math.abs(q.perp) end)
            -- pocket beside a blocker: s = chord side, D = rim
            -- clearance, du = chord-param shift along the travel
            -- direction (0 = beside the node's centre)
            local function pocket(nod, s, D, du)
                return {x = nod.x - uy * s * (G.NODE_R + D)
                             - ux * du * dl,
                        y = nod.y + ux * s * (G.NODE_R + D)
                             + uy * du * dl,
                        u = math.max(0.15,
                                 math.min(0.85, nod.u + du))}
            end
            -- quadratic through W at u: C = (W - ((1-u)^2 A + u^2 B))
            -- / 2u(1-u) — the curve passes exactly through W
            local function bez2_through(w, nseg)
                local u, den = w.u, 2 * w.u * (1 - w.u)
                local cx = (w.x - (1 - u) ^ 2 * ax - u * u * tx) / den
                local cy = (w.y - (1 - u) ^ 2 * ay - u * u * ty) / den
                return geo.bez2({}, ax, ay, cx, cy, tx, ty, nseg or 24)
            end
            -- cubic through W1@u1, W2@u2: solve the 2x2 system for
            -- both control points (same matrix for x and y)
            local function bez3_through(w1, w2, nseg)
                local u1, u2 = w1.u, w2.u
                local b1 = 3 * (1 - u1) ^ 2 * u1
                local c1 = 3 * (1 - u1) * u1 ^ 2
                local b2 = 3 * (1 - u2) ^ 2 * u2
                local c2 = 3 * (1 - u2) * u2 ^ 2
                local det = b1 * c2 - b2 * c1
                if math.abs(det) < 1e-4 then return nil end
                local r1x = w1.x - (1 - u1) ^ 3 * ax - u1 ^ 3 * tx
                local r1y = w1.y - (1 - u1) ^ 3 * ay - u1 ^ 3 * ty
                local r2x = w2.x - (1 - u2) ^ 3 * ax - u2 ^ 3 * tx
                local r2y = w2.y - (1 - u2) ^ 3 * ay - u2 ^ 3 * ty
                local c1x = (r1x * c2 - r2x * c1) / det
                local c1y = (r1y * c2 - r2y * c1) / det
                local c2x = (b1 * r2x - b2 * r1x) / det
                local c2y = (b1 * r2y - b2 * r1y) / det
                return geo.bez3({}, ax, ay, c1x, c1y, c2x, c2y,
                                tx, ty, nseg or 24)
            end
            -- polyline through the waypoints with ROUNDED corners:
            -- each waypoint becomes the control of a small quadratic,
            -- the legs stay straight — reads as a guided route while
            -- still hugging the corridor exactly (the literal
            -- "Haltepunkte" route).  Legs are subdivided to ~10px so
            -- viol()'s vertex-based near-miss scan actually sees a
            -- mid-leg graze, not just the waypoints
            local function poly_through(ws)
                local p0 = {ax, ay}
                local function leg(x1, y1, x2, y2)
                    local n = math.max(1,
                        math.ceil(math.sqrt((x2 - x1) ^ 2
                                          + (y2 - y1) ^ 2) / 10))
                    for k = 1, n do
                        p0[#p0 + 1] = x1 + (x2 - x1) * k / n
                        p0[#p0 + 1] = y1 + (y2 - y1) * k / n
                    end
                end
                local pts = {ax, ay}
                for _, w in ipairs(ws) do
                    pts[#pts + 1] = w.x
                    pts[#pts + 1] = w.y
                end
                pts[#pts + 1] = tx
                pts[#pts + 1] = ty
                local px, py = pts[1], pts[2]
                for k = 3, #pts - 2, 2 do   -- interior waypoints
                    local wx, wy = pts[k], pts[k + 1]
                    local nx, ny = pts[k + 2], pts[k + 3]
                    local d1 = math.sqrt((wx - px) ^ 2 + (wy - py) ^ 2)
                    local d2 = math.sqrt((nx - wx) ^ 2 + (ny - wy) ^ 2)
                    local r = math.min(30, d1 * 0.45, d2 * 0.45)
                    if d1 < 1 or d2 < 1 or r < 4 then
                        leg(px, py, wx, wy)
                        px, py = wx, wy
                    else
                        local ix, iy = wx - (wx - px) / d1 * r,
                                       wy - (wy - py) / d1 * r
                        local ox, oy = wx + (nx - wx) / d2 * r,
                                       wy + (ny - wy) / d2 * r
                        leg(px, py, ix, iy)
                        local b = geo.bez2({}, ix, iy, wx, wy, ox, oy, 8)
                        for j = 3, #b do p0[#p0 + 1] = b[j] end
                        px, py = ox, oy
                    end
                end
                leg(px, py, tx, ty)
                return p0
            end
            -- label anchor: route midpoint; h=0 sends the label to
            -- the straight-chord branch (side_score picks the free
            -- side off the route mid)
            local function take(p0, s)
                if not p0 then return end
                local v = viol(p0)
                if DBG_EDGE == i then
                    print(string.format("  e%d cand via s=%d viol=%.1f",
                                        i, s, v))
                end
                local mx, my = poly_at(p0, 0.5)
                local cand = {v = v, hh = 0, kind = "via", via = p0,
                              apx = mx, apy = my}
                if v <= 0 and not via_best then via_best = cand end
                if not via_min or v < via_min.v then via_min = cand end
                if not best or v < best.v - 0.5
                   or (math.abs(v - best.v) <= 0.5
                       and poly_dev(p0) + 1
                           < poly_dev(best._poly or best.via)) then
                    best = cand
                end
            end
            arc_best = best  -- min viol over arc/bez only
            -- waypoint routes are the polish pass — skip them while
            -- dragging (the settle frame re-runs the full scan)
        if not G.dragging then
            -- flat WIRE sweep: perpendicular legs out of both rims,
            -- a level plateau across the chord — the "up, across,
            -- down" route.  The legs land on rim slots FAR from the
            -- tips of chord-direction siblings, so it clears exactly
            -- the rim-slot crowding that forces a plain bow deep
            -- (q3->q0 over q1,q2 used to arc ~100px above the rims)
            for _, s in ipairs{pref, -pref} do
                for _, L in ipairs{10, 22, 34, 50} do
                    local lift = G.NODE_R + L
                    take(clip_rims(poly_through{
                        {x = ax - uy * s * lift,
                         y = ay + ux * s * lift},
                        {x = tx - uy * s * lift,
                         y = ty + ux * s * lift}}), s)
                end
            end
            local n1, n2 = blockers[1], blockers[2]
            -- pockets/channels wrap EVERY chord blocker, not just the
            -- nearest: the only clean corridor can sit behind the
            -- SECOND blocker (e.g. a sibling lens hugging the first)
            for _, n1 in ipairs(blockers) do
                -- pocket on the far side of the blocker first — the
                -- wrap-around reading; the chord-side squeeze second.
                -- Wider pockets thread looser corridors (e.g. past a
                -- bidirectional lens sitting behind the blocker)
                local sf = n1.perp >= 0 and 1 or -1
                for _, s in ipairs{sf, -sf} do
                    for _, D in ipairs{14, 30, 50} do
                        take(clip_rims(
                            bez2_through(pocket(n1, s, D, 0))), s)
                    end
                end
                -- one blocker, single pocket still dirty: wrap around
                -- it with TWO waypoints — before/after the node on
                -- the same side, so the cubic hugs its flank
                for _, s in ipairs{sf, -sf} do
                    for _, D in ipairs{14, 34} do
                        local raw = bez3_through(
                            pocket(n1, s, D, -0.16),
                            pocket(n1, s, D, 0.16))
                        take(raw and clip_rims(raw), s)
                        -- sharp-cornered variant: the waypoint pair as
                        -- real polyline bends — the last thing tried
                        take(clip_rims(poly_through{
                            pocket(n1, s, D, -0.16),
                            pocket(n1, s, D, 0.16)}), s)
                    end
                    -- and the CHANNEL shape: out around the blocker,
                    -- straight down the far side, entering the target
                    -- rim from that side — needed when a foreign
                    -- route hugs the chord's end region (a pocket
                    -- pair at ±du still dives back too early).
                    -- A first waypoint beside the SOURCE rim steers
                    -- the departure off siblings' tail slots
                    for _, D in ipairs{14, 34} do
                        local w0 = {
                            x = ax - uy * s * (G.NODE_R + 20)
                                     + ux * (G.NODE_R + 14),
                            y = ay + ux * s * (G.NODE_R + 20)
                                     + uy * (G.NODE_R + 14)}
                        for _, D2 in ipairs{30, 48} do
                            -- approach tilt: f=0 is the plain side
                            -- approach; f>0 rotates the rim landing
                            -- along the rim toward the chord's travel
                            -- direction — needed when the side slot
                            -- is already taken by a RESOLVED sibling
                            -- leaving/entering the target
                            for _, f in ipairs{0, 0.8, 1.6} do
                                local dx2 = -uy * s + ux * f
                                local dy2 = ux * s + uy * f
                                local dn = math.sqrt(dx2 * dx2
                                                   + dy2 * dy2)
                                local w2 = {
                                    x = tx + dx2 / dn
                                             * (G.NODE_R + D2),
                                    y = ty + dy2 / dn
                                             * (G.NODE_R + D2)}
                                take(clip_rims(poly_through{w0,
                                    pocket(n1, s, D, 0), w2}), s)
                            end
                        end
                    end
                end
            end
            if n1 and n2 and math.abs(n1.u - n2.u) > 0.18 then
                for _, s1 in ipairs{-1, 1} do
                    for _, s2 in ipairs{-1, 1} do
                        local raw = bez3_through(pocket(n1, s1, 14, 0),
                                                 pocket(n2, s2, 14, 0))
                        take(raw and clip_rims(raw), s1)
                    end
                end
            end
        end
        end
        -- Winner selection:
        --   1. a clean simple route — the normal case (a clean
        --      corridor route still beats a DEEP clean sweep: that
        --      sweep is why via routes were tried, |hh| > 0.30·dl)
        --   2. otherwise the least-dirty SIMPLE route — UNLESS a
        --      waypoint route beats it by a real margin
        --      (15 ≈ one crossing): a slight graze or rim crowding
        --      on a straight/arc line reads far better than a
        --      multi-waypoint squiggle (2.1C q3->q5)
        if clean_best then
            best = via_best or clean_best
        elseif arc_best
           and (not via_min or arc_best.v < via_min.v + 15) then
            best = arc_best
        elseif via_min then
            best = via_min
        end
        best = best or {hh = h, kind = "arc"}
        -- hysteresis on RE-resolution (the fixpoint pass feeds the
        -- previous route in as keep_route): keep it unless the new
        -- winner is clearly better — symmetric choices would
        -- otherwise oscillate from one iteration to the next.
        -- BUT a violation tie must not entrench a DEEP route the
        -- drag pass settled for: drag frames skip the via sweep, so
        -- a clean deep arc can sit in keep_route while a clean
        -- shallow wire exists — shallowness then decides
        local keep_old = false
        if keep_route and keep_route._ax
           and (best.v or math.huge) >= viol(keep_route) - 8 then
            keep_old = true
            local bp = best.via or best._poly
            if best.v and best.v <= viol(keep_route)
               and bp and poly_dev(bp) + 30
                          < poly_dev(keep_route) then
                keep_old = false
            end
        end
        if keep_old then
            pts, h = keep_route, keep_route._hh or 0
            apx, apy = keep_route._ax, keep_route._ay
            nlx, nly = keep_route._nx, keep_route._ny
        elseif best.kind == "via" then
            pts = best.via
            apx, apy = best.apx, best.apy
            nlx, nly = -uy, ux   -- chord normal; h==0 relabels anyway
            h = best.hh
        else
            pts, apx, apy, nlx, nly =
                (best.kind == "bez" and build_bez or build_arc)(best.hh)
            h = best.hh
        end
        in_clear = false
    else
        -- no obstacles seen (or nested call): base geometry as decided
        pts, apx, apy, nlx, nly = build_arc(h)
    end
    -- label distance keeps the TEXT BOX off the line: the box reaches
    -- toward the edge by (tw/2)|nx| + (fh/2)|ny|, so a horizontal
    -- label needs more offset on a diagonal than on a horizontal edge
    local tw = (A.text_width and A.text_width(e.label, -1))
               or #e.label * 5
    local lx, ly
    if h == 0 then
        -- straight chord: normal is undefined in arc_poly; put the
        -- label on the side with more free space (other states and
        -- transitions push it out of the crowded region)
        local mx, my = apx, apy
        local off = 2 + tw * 0.5 * math.abs(uy) + fh * 0.5 * math.abs(ux)
        nlx, nly = -uy, ux
        if not geo_only then
            local s1 = side_score(mx + nlx * off, my + nly * off,
                                  i, bx, by, vox, voy)
            local s2 = side_score(mx - nlx * off, my - nly * off,
                                  i, bx, by, vox, voy)
            if s2 < s1 then nlx, nly = -nlx, -nly end
        end
        lx, ly = mx + nlx * off, my + nly * off
    else
        local off = 2 + tw * 0.5 * math.abs(nlx)
                      + fh * 0.5 * math.abs(nly)
        lx, ly = apx + nlx * off, apy + nly * off
    end
    -- the route is final BEFORE the label search: store it now so a
    -- sibling resolving during our own label phase sees the real arc
    -- (nlx/nly are final here — straight chords only choose their
    -- side above)
    if not in_clear and not route_res[i] then
        pts._ax, pts._ay, pts._nx, pts._ny = apx, apy, nlx, nly
        pts._hh = h
        route_res[i], route_bb[i] = pts, poly_bb(pts)
    end
    if not geo_only and e.label ~= "" and not G.dragging then
        -- two-phase placement: every route must be resolved before
        -- the first label is placed — label_viol needs each
        -- sibling's REAL arc, not its base guess
        resolve_all(bx, by, vox, voy, fh)
        -- the resweep may have re-routed THIS edge — refresh our
        -- copy and its anchors before placing the label
        pts = route_res[i]
        apx, apy, nlx, nly = pts._ax, pts._ay, pts._nx, pts._ny
        -- label candidate search: anchors at u=0.5/0.3/0.7 along the
        -- curve (arc length — works for straight chords too), each
        -- with its LOCAL normal so candidates can slide along the
        -- curve, pushed to both sides at growing offsets
        local anchs = {{x = apx, y = apy, nx = nlx, ny = nly}}
        for _, u in ipairs{0.3, 0.7} do
            local ux2, uy2 = poly_at(pts, u)
            local tdx, tdy = poly_dir(pts, u)
            anchs[#anchs + 1] = {x = ux2, y = uy2,
                                 nx = -tdy, ny = tdx}
        end
        lx, ly = pick_label(i, bx, by, vox, voy, fh, tw, anchs)
    end
    if not in_clear and not geo_only then
        lbl_pos[i] = {x = lx, y = ly, w = tw}
    end
    return pts, lx, ly
end
aut.edge_siblings = edge_siblings

-- ---------------------------------------------------------------------
-- hit tests (screen coords — the skeleton passes pointer positions)
local function hit_node_r(px, py, r)
    local cb = G.canvas
    for i = 1, #G.nodes do
        local n = G.nodes[i]
        local dx = px - (cb.x + (cb.ox or 0) + n.x)
        local dy = py - (cb.y + (cb.oy or 0) + n.y)
        if dx * dx + dy * dy < r * r then return i end
    end
    return nil
end

local function hit_node(px, py) return hit_node_r(px, py, G.NODE_R) end

local function hit_edge_i(i, px, py, halfw)
    -- PEEK, never resolve: a hover test running before the draw pass
    -- must not decide resolution ORDER — an early edge resolving
    -- against mere base geometry of its siblings can lock itself into
    -- a needlessly deep route.  in_clear makes the call return the
    -- already-resolved route or cheap base geometry, unstored.
    local wc = in_clear
    in_clear = true
    local pts = aut.edge_poly(i, G.canvas.x, G.canvas.y,
                              G.canvas.ox or 0, G.canvas.oy or 0,
                              nil, true)
    in_clear = wc
    if not pts then return false end
    if geo.poly_dist(pts, px, py) < halfw then return true end
    -- the label IS the edge's handle: hovering the text must light
    -- the same edge the pointer would hit on its arc — and a click
    -- there must select that edge, not spawn a state next to it
    local L = lbl_pos[i]
    local e = G.edges[i]
    if L and e and (e.label or "") ~= "" then
        local hw = L.w * 0.5 + 2
        local hh = (L.h or 14) * 0.5 + 2
        if px >= L.x - hw and px <= L.x + hw
           and py >= L.y - hh and py <= L.y + hh then
            return true
        end
    end
    return false
end

local function hit_edge(px, py, halfw)
    for i = 1, #G.edges do
        if hit_edge_i(i, px, py, halfw) then return i end
    end
    return nil
end

-- ---------------------------------------------------------------------
-- scene drawing
local H_CLEAR = pk({0, 0, 0, 0})   -- transparent text background

local function aut_draw(canvas, ctx)
    local cb = G.canvas
    local bx, by = ctx.bx, ctx.by
    local vox, voy = ctx.vox, ctx.voy
    local mx, my, fh = ctx.mx, ctx.my, ctx.fh

    A.fill_rect(canvas, ctx.vx0, ctx.vy0, cb.vw, cb.vh, 0.0,
                col(TH.GREY_XLIGHT))
    A.stroke_rect(canvas, ctx.vx0, ctx.vy0, cb.vw, cb.vh, 0.0, 1.0,
                  col(TH.GREY_LIGHT))

    -- resolve all routes BEFORE drawing anything: draw order owns
    -- resolution order, and the resweep washes out order artefacts —
    -- also needed for all-unlabelled automata where no label phase
    -- would ever trigger resolve_all
    resolve_all(bx, by, vox, voy, fh)

    -- transitions first so states paint over arrow tails; label
    -- anchors are collected and drawn LAST (below) so a label never
    -- ends up underneath a state circle
    local lbl = {}
    for i = 1, #G.edges do
        local pts, lx, ly = aut.edge_poly(i, bx, by, vox, voy, fh)
        if pts then
            local e = G.edges[i]
            local sel = (G.sel_edge == i)
            local hov = (G.hov_edge == i)
            local pr = G.prob_edges and G.prob_edges[e.id]
            -- a reported problem outranks hover/selection colouring —
            -- the red/amber IS the information here
            local ec = pr == "error" and C_RED
                       or pr and C_AMBER
                       or (sel or hov) and TH.BLUE
                       or (G.sim_edges and G.sim_edges[e.id] and C_SIM_E)
                       or (e.locked and C_LOCK_E or TH.GREY_DARK)
            local n = #pts / 2
            local buf = pbuf_for(#pts)
            for j = 1, #pts do buf[j - 1] = pts[j] end
            A.stroke_polyline(canvas, buf, n,
                              sel and 3.5 or (hov and 2.5 or 2.0),
                              pk(ec))
            -- arrowhead: tip on the rim, BASE MIDPOINT exactly on the
            -- edge (arrow length back along the polyline).  The axis
            -- base->tip therefore follows the incoming curve instead
            -- of the radial line — on curved routes the head reads as
            -- the stroke's continuation, not a radial skew
            local ex, ey = pts[#pts - 1], pts[#pts]
            local mx2, my2 = poly_back(pts, 10.0)
            local ax2, ay2 = ex - mx2, ey - my2
            local al = math.sqrt(ax2 * ax2 + ay2 * ay2)
            local ux, uy
            if al > 1e-6 then
                ux, uy = ax2 / al, ay2 / al
            else
                ux, uy = geo.poly_end_dir(pts)
            end
            local px, py = -uy, ux
            local aw = (sel or hov) and 6.5 or 5.0
            A.fill_triangle(canvas, ex, ey,
                mx2 + px * aw, my2 + py * aw,
                mx2 - px * aw, my2 - py * aw,
                col(ec))
            lbl[#lbl + 1] = {i = i, x = lx, y = ly, ec = ec}
        end
    end

    -- connect gesture: straight preview ray, or a loop ghost when the
    -- pointer sits on the source state (drop = self-transition)
    if G.connecting and ctx.connect_from then
        if G.hovered == G.connecting then
            local sn = G.nodes[G.connecting]
            local pts = geo.loop_arc({}, bx + vox + sn.x,
                                     by + voy + sn.y, G.NODE_R)
            local buf = pbuf_for(#pts)
            for j = 1, #pts do buf[j - 1] = pts[j] end
            A.stroke_polyline(canvas, buf, #pts / 2, 1.5,
                              pk({0, 125, 156, 153}))
        else
            gw.connect_preview(canvas, ctx)
        end
    end

    for i = 1, #G.nodes do
        local n = G.nodes[i]
        local nx, ny = bx + vox + n.x, by + voy + n.y
        if nx + G.NODE_R + 6 >= ctx.vx0 and nx - G.NODE_R - 6 <= ctx.vx1
           and ny + G.NODE_R + 6 >= ctx.vy0
           and ny - G.NODE_R - 6 <= ctx.vy1 then
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
        -- a live simulation configuration paints over everything but
        -- the selection border (problems keep theirs)
        if G.sim_live and G.sim_live[n.id] then fill = C_SIM end
        -- selection wins the border in every fill state so a selected
        -- problem-state is still visibly selected (thick blue ring)
        if i == G.selected then
            border = TH.DARKBLUE
            if not pr then fill = TH.BLUE end
        end
        if G.connecting and i == G.hovered then
            border = TH.BLUE
        end
        if on_handle then handle = TH.BLUE end

        A.fill_circle(canvas, nx - G.NODE_R, ny - G.NODE_R,
                      G.NODE_R * 2, G.NODE_R * 2, col(fill))
        A.stroke_circle(canvas, nx - G.NODE_R, ny - G.NODE_R,
                        G.NODE_R * 2, G.NODE_R * 2,
                        i == G.selected and 3.5 or 2.0, col(border))
        -- accepting: double ring
        if n.accepting then
            local r = G.NODE_R - 4
            A.stroke_circle(canvas, nx - r, ny - r, r * 2, r * 2,
                            1.6, col(border))
        end
        -- the component's OWN former final state: dashed grey ring,
        -- a bit inside the accepting ring so both can coexist
        if n.seed_exit then
            dash_ring(canvas, nx, ny, G.NODE_R - 7, 1.6, C_SEED_MK)
        end
        -- initial marker: a normal arrow into the state, placed on the
        -- side facing AWAY from incident edges (same free-space rule
        -- as self-loops); falls back to the left
        local idir_used
        if n.initial then
            local da = free_dir(n, math.pi)
            idir_used = da
            local dc, ds = math.cos(da), math.sin(da)
            local ix, iy = nx + dc * G.NODE_R, ny + ds * G.NODE_R
            A.stroke_line(canvas, ix + dc * 24, iy + ds * 24,
                          ix + dc * 2, iy + ds * 2, 2.0, col(border))
            A.fill_triangle(canvas, ix, iy,
                ix + dc * 9 - ds * 4.5, iy + ds * 9 + dc * 4.5,
                ix + dc * 9 + ds * 4.5, iy + ds * 9 - dc * 4.5,
                col(border))
        end
        -- the component's OWN former initial state: dashed grey arrow,
        -- offset from the live initial arrow when both are present
        if n.seed_entry then
            local sa = free_dir(n, math.pi,
                                idir_used and {idir_used} or nil)
            local sc, ss = math.cos(sa), math.sin(sa)
            local ix, iy = nx + sc * G.NODE_R, ny + ss * G.NODE_R
            dash_line(canvas, ix + sc * 26, iy + ss * 26,
                      ix + sc * 2, iy + ss * 2, 1.6, C_SEED_MK)
            A.stroke_line(canvas, ix, iy,
                ix + sc * 9 - ss * 4.5, iy + ss * 9 + sc * 4.5,
                1.6, col(C_SEED_MK))
            A.stroke_line(canvas, ix, iy,
                ix + sc * 9 + ss * 4.5, iy + ss * 9 - sc * 4.5,
                1.6, col(C_SEED_MK))
        end
        if i == G.hovered and not G.connecting then
            A.stroke_circle(canvas, nx - G.CONNECT_R, ny - G.CONNECT_R,
                            G.CONNECT_R * 2, G.CONNECT_R * 2, 1.0,
                            col(TH.GREY))
        end
        -- the connect disc only shows under the pointer — drawn over
        -- the state name it just looks wrong when always on
        if i == G.hovered then
            A.fill_circle(canvas, nx - G.NODE_C, ny - G.NODE_C,
                          G.NODE_C * 2, G.NODE_C * 2, col(handle))
            A.stroke_circle(canvas, nx - G.NODE_C, ny - G.NODE_C,
                            G.NODE_C * 2, G.NODE_C * 2, 1.0,
                            col(TH.GREY_DARK))
        end
        -- the state name inside the circle; a problem fill stays
        -- pale, so white selected-text would vanish on it
        local tw = A.text_width(n.name, -1)
        local tc = (i == G.selected and not pr) and TH.WHITE
                   or TH.BLACK
        A.draw_text(canvas, nx - tw * 0.5, ny - fh * 0.5, tw, fh,
                    n.name, -1, H_CLEAR, pk(tc))
        end
    end

    -- transition labels on top of everything inside the scissor; the
    -- text colour follows the edge's state colour so the pairing is
    -- unmistakable (no background box — nk_convert ignores draw_text's
    -- bg arg anyway)
    for _, L in ipairs(lbl) do
        local e = G.edges[L.i]
        if e.label ~= "" then
            local tw = A.text_width(e.label, -1)
            A.draw_text(canvas, L.x - tw * 0.5, L.y - fh * 0.5,
                        tw, fh, e.label, -1, H_CLEAR, pk(L.ec))
        end
    end
end

-- states snap to an invisible GRID² lattice (keeps automata tidy for
-- students; nothing is drawn at the grid points).  G.GRID is set per
-- frame, so fall back to the unscaled cell size when a model load
-- runs before the first frame
local function snap_pt(x, y)
    local g = G.GRID or 66.0
    return math.max(g, math.floor(x / g + 0.5) * g),
           math.max(g, math.floor(y / g + 0.5) * g)
end

-- lattice cells already taken, except_id leaves one state out (the
-- dragged node, or the node being resolved during destack)
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

-- two states sharing a lattice cell stack exactly and hide each
-- other (the classic "missing transitions from q3" confusion), so a
-- snap on an occupied cell resolves to the nearest FREE cell: adds
-- and drops land beside an occupied spot instead of stacking
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
                        if not fd or d < fd then fx, fy, fd = cx, cy, d end
                    end
                end
            end
        end
        if fx then return fx, fy end
    end
    return sx, sy   -- dense beyond reason: tolerate the overlap
end

local AUT_OPS = {
    hit_node = hit_node,
    hit_edge = hit_edge,
    hit_edge_i = hit_edge_i,
    add_node = function(_, x, y)
        model.add_state(G, snap_free(x, y))
    end,
    add_edge = function(_, from, to) model.add_transition(G, from, to) end,
    -- a finished drag is a state edit too — positions are part of the
    -- saved model, so on_changed must count it for autosave/notify
    moved = function()
        if model.on_changed then model.on_changed() end
    end,
    snap = snap_free,
    self_loop = true,
    draw = aut_draw,
    -- Anubis review mode (ui_readonly -> G.readonly): hover/select
    -- still work, all mutation gestures are gated inside gw.widget
    readonly = function() return G.readonly end,
    -- and no edit affordance in the pointer either — plain arrow
    cursor = function(ctx, S)
        if G.readonly then return nil end
        return gw.default_cursor(ctx, S)
    end,
}

function aut.widget(height, width)
    return gw.widget(height, width, G, AUT_OPS)
end

-- a saved/imported model may already carry stacked states (created
-- before the free-cell snap): resolve any overlap once per load so
-- hidden states become visible again; registered on G so
-- model.load() picks it up on every load path
function aut.destack()
    for _, n in ipairs(G.nodes) do
        local cx, cy = snap_pt(n.x, n.y)
        if occ_cells(n.id)[cx .. "," .. cy] then
            n.x, n.y = snap_free(n.x, n.y, n.id)
        end
    end
end
G.destack = aut.destack

aut.hit_node   = hit_node
aut.hit_edge   = hit_edge
aut.hit_edge_i = hit_edge_i
aut.free_dir   = free_dir   -- initial-marker direction for exporters
aut.ops        = AUT_OPS
return aut
