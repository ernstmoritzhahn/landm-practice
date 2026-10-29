-- ui/geom.lua -- pure 2-D geometry helpers for the canvas widgets.
-- No editor state, no bridge calls: the same functions are used by the
-- label engine (ui/label.lua) and the temp-graph router (tmp_nodes.lua).

local geo = {}

-- signed distances: a point inside the rect (or an overlapping rect)
-- yields a negative value, so a candidate that overlaps an obstacle is
-- scored worse than one that merely touches it
function geo.rect_pt_dist(rx, ry, rw, rh, px, py)
    local dx = math.max(rx - px, 0, px - (rx + rw))
    local dy = math.max(ry - py, 0, py - (ry + rh))
    if dx == 0 and dy == 0 then
        return -math.min(px - rx, rx + rw - px, py - ry, ry + rh - py)
    end
    return math.sqrt(dx * dx + dy * dy)
end

function geo.rect_rect_dist(ax, ay, aw, ah, qx, qy, qw, qh)
    local dx = math.max(ax - (qx + qw), qx - (ax + aw))
    local dy = math.max(ay - (qy + qh), qy - (ay + ah))
    if dx < 0 and dy < 0 then
        -- overlap: negative of the shallower push-apart axis
        return math.max(dx, dy)
    end
    dx, dy = math.max(dx, 0), math.max(dy, 0)
    return math.sqrt(dx * dx + dy * dy)
end

-- distance from point (px,py) to segment (ax,ay)-(bx,by)
function geo.pt_seg_dist(px, py, ax, ay, bx, by)
    local vx, vy = bx - ax, by - ay
    local L2 = vx * vx + vy * vy
    local t = L2 > 1e-9
              and math.max(0, math.min(1,
                       ((px - ax) * vx + (py - ay) * vy) / L2))
              or 0
    local dx, dy = px - ax - vx * t, py - ay - vy * t
    return math.sqrt(dx * dx + dy * dy)
end

function geo.segs_cross(ax, ay, bx, by, cx, cy, dx, dy)
    local s1 = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)
    local s2 = (bx - ax) * (dy - ay) - (by - ay) * (dx - ax)
    local s3 = (dx - cx) * (ay - cy) - (dy - cy) * (ax - cx)
    local s4 = (dx - cx) * (by - cy) - (dy - cy) * (bx - cx)
    return (s1 > 0) ~= (s2 > 0) and (s3 > 0) ~= (s4 > 0)
end

-- distance between an axis-aligned rect and a segment: negative when
-- they overlap (mirroring rect_pt_dist's inside convention).  Exact —
-- label_pos used to sample a few points per edge and a long edge
-- passing close BETWEEN samples read as clear.
function geo.rect_seg_dist(rx, ry, rw, rh, ax, ay, bx, by)
    local d = math.min(geo.rect_pt_dist(rx, ry, rw, rh, ax, ay),
                       geo.rect_pt_dist(rx, ry, rw, rh, bx, by),
                       geo.pt_seg_dist(rx,      ry,      ax, ay, bx, by),
                       geo.pt_seg_dist(rx + rw, ry,      ax, ay, bx, by),
                       geo.pt_seg_dist(rx,      ry + rh, ax, ay, bx, by),
                       geo.pt_seg_dist(rx + rw, ry + rh, ax, ay, bx, by))
    if d <= 0 then return d end   -- an endpoint is inside the rect
    if geo.segs_cross(ax, ay, bx, by, rx,      ry,      rx + rw, ry)
       or geo.segs_cross(ax, ay, bx, by, rx + rw, ry,      rx + rw, ry + rh)
       or geo.segs_cross(ax, ay, bx, by, rx + rw, ry + rh, rx,      ry + rh)
       or geo.segs_cross(ax, ay, bx, by, rx,      ry + rh, rx,      ry) then
        return -d    -- crossing: negative with the separation magnitude
    end
    return d
end

-- parametric proper-intersection test (tmp_nodes' route detours): true
-- only for crossings strictly inside both segments; parallel and
-- endpoint touches do not count.
function geo.segments_intersect(ax, ay, bx, by, cx, cy, dx, dy)
    local function cross(ux, uy, vx, vy) return ux * vy - uy * vx end
    local rx, ry = bx - ax, by - ay
    local sx, sy = dx - cx, dy - cy
    local d = cross(rx, ry, sx, sy)
    if math.abs(d) < 1e-9 then return false end -- parallel/collinear
    local t = cross(cx - ax, cy - ay, sx, sy) / d
    local u = cross(cx - ax, cy - ay, rx, ry) / d
    return t > 1e-6 and t < 1 - 1e-6 and u > 1e-6 and u < 1 - 1e-6
end

-- ===== curves --------------------------------------------------------
-- Edges as tessellated curves in flat {x1,y1,x2,y2,…} form: one point
-- list feeds stroke_polyline (drawing), poly_dist (hit-testing) and the
-- arrowhead tangent.

-- circular-arc segment, tessellated: the arc of the circle
-- (ox,oy,r) swept from angle ts to angle te THROUGH angle ta — i.e.
-- whichever of the two complementary arcs contains ta (minor or major).
-- Segment count scales with arc length so short bows and ~300° loops
-- both come out smooth.  Returns out plus the exact apex point.
local TAU = 2 * math.pi
local function angnorm(x)          -- to (-pi, pi]
    x = math.fmod(x, TAU)
    if x <= -math.pi then x = x + TAU
    elseif x > math.pi then x = x - TAU end
    return x
end

function geo.arc_seg(out, ox, oy, r, ts, te, ta, n)
    local d = angnorm(te - ts)
    local da = angnorm(ta - ts)
    -- is ta strictly inside the direct sweep from ts to te?
    if not ((d > 0 and da > 0 and da < d)
            or (d < 0 and da < 0 and da > d)) then
        d = d > 0 and d - TAU or d + TAU   -- take the complementary arc
    end
    n = n or math.max(8, math.min(96,
              math.ceil(math.abs(d) * r / 4)))
    for i = 0, n do
        local a = ts + d * (i / n)
        out[#out + 1] = ox + math.cos(a) * r
        out[#out + 1] = oy + math.sin(a) * r
    end
    return out
end

-- arc between two points with a given sagitta h (signed perpendicular
-- offset of the apex from the chord midpoint; +h = left of travel).
-- h ~ 0 degenerates to a straight segment.  Returns out, apex x/y and
-- the unit chord normal pointing toward the apex side.
function geo.arc_poly(out, sx, sy, ex, ey, h, n)
    if math.abs(h) < 1e-3 then
        out[#out + 1] = sx
        out[#out + 1] = sy
        out[#out + 1] = ex
        out[#out + 1] = ey
        return out, (sx + ex) * 0.5, (sy + ey) * 0.5, 0, 0
    end
    local dx, dy = ex - sx, ey - sy
    local L = math.sqrt(dx * dx + dy * dy)
    if L < 1e-6 then return nil end
    local nlx, nly = -dy / L * (h > 0 and 1 or -1),
                     dx / L * (h > 0 and 1 or -1)
    local mx, my = (sx + ex) * 0.5, (sy + ey) * 0.5
    local ah = math.abs(h)
    local r = (L * L / 4 + ah * ah) / (2 * ah)
    -- centre sits on the perpendicular bisector; on the side opposite
    -- the apex for minor arcs (ah < L/2), same side for major ones —
    -- the signed form (r - ah) covers both
    local ox = mx - nlx * (r - ah)
    local oy = my - nly * (r - ah)
    local apx, apy = mx + nlx * ah, my + nly * ah
    geo.arc_seg(out, ox, oy, r,
                math.atan2(sy - oy, sx - ox),
                math.atan2(ey - oy, ex - ox),
                math.atan2(apy - oy, apx - ox), n)
    return out, apx, apy, nlx, nly
end

-- self-loop on a state circle as a true circular arc: a loop circle of
-- radius rl sits on the rim along `dir` so it meets the node at the two
-- rim points dir±psi, and its top reaches cx + H*d(dir).  The drawn arc
-- is the major sweep through the apex — exits the rim on one side, loops
-- around, re-enters on the other.  Returns out, apex x/y.
function geo.loop_arc(out, cx, cy, R, dir, psi, H, n)
    dir = dir or -math.pi * 0.5
    psi = psi or 0.45
    H = H or 2.3 * R
    local cd, sd = math.cos(dir), math.sin(dir)
    -- centre distance along dir from the rim-point+apex constraints:
    -- |P± - O| = rl and apex = O + rl*d => k = (H^2 - R^2)/(2(H - R cos psi))
    local k = (H * H - R * R) / (2 * (H - R * math.cos(psi)))
    local rl = H - k
    local ox, oy = cx + cd * k, cy + sd * k
    local sx = cx + math.cos(dir + psi) * R
    local sy = cy + math.sin(dir + psi) * R
    local ex = cx + math.cos(dir - psi) * R
    local ey = cy + math.sin(dir - psi) * R
    local apx, apy = cx + cd * H, cy + sd * H
    geo.arc_seg(out, ox, oy, rl,
                math.atan2(sy - oy, sx - ox),
                math.atan2(ey - oy, ex - ox),
                math.atan2(apy - oy, apx - ox), n)
    return out, apx, apy
end

-- quadratic bezier, n segments appended to out (n defaults 16)
function geo.bez2(out, x0, y0, cx, cy, x1, y1, n)
    n = n or 16
    for i = 0, n do
        local t = i / n
        local u = 1 - t
        out[#out + 1] = u * u * x0 + 2 * u * t * cx + t * t * x1
        out[#out + 1] = u * u * y0 + 2 * u * t * cy + t * t * y1
    end
    return out
end

-- cubic bezier, n segments appended to out
function geo.bez3(out, x0, y0, x1, y1, x2, y2, x3, y3, n)
    n = n or 20
    for i = 0, n do
        local t = i / n
        local u = 1 - t
        local a, b = u * u, 3 * u * t
        out[#out + 1] = u * a * x0 + 3 * a * t * x1 + b * t * x2 + t * t * t * x3
        out[#out + 1] = u * a * y0 + 3 * a * t * y1 + b * t * y2 + t * t * t * y3
    end
    return out
end

-- distance from point to a flat polyline; nil/short inputs give huge
function geo.poly_dist(pts, px, py)
    local best = math.huge
    for i = 1, (pts and #pts or 0) - 2, 2 do
        local d = geo.pt_seg_dist(px, py, pts[i], pts[i + 1],
                                  pts[i + 2], pts[i + 3])
        if d < best then best = d end
    end
    return best
end

-- unit direction of a polyline's last non-degenerate segment (for the
-- arrowhead); falls back to +x
function geo.poly_end_dir(pts)
    local n = #pts   -- last point is (pts[n-1], pts[n]); xs at odd idx
    for i = n - 3, 1, -2 do
        local dx, dy = pts[n - 1] - pts[i], pts[n] - pts[i + 1]
        local len = math.sqrt(dx * dx + dy * dy)
        if len > 1e-6 then return dx / len, dy / len end
    end
    return 1, 0
end

-- directed edge between two circle centres: endpoints trimmed onto the
-- rims; bow != 0 bows the curve perpendicular (positive = left of the
-- travel direction) so opposite-direction pairs separate.  Returns
-- sx,sy, ex,ey, cx,cy (bez2 control; cx,cy == midpoint when bow == 0).
function geo.edge_geom(ax, ay, ar, bx, by, br, bow)
    local dx, dy = bx - ax, by - ay
    local len = math.sqrt(dx * dx + dy * dy)
    if len < 1e-6 then return nil end
    local ux, uy = dx / len, dy / len
    local sx, sy = ax + ux * ar, ay + uy * ar
    local ex, ey = bx - ux * br, by - uy * br
    local cx, cy = (sx + ex) * 0.5 - uy * bow,
                   (sy + ey) * 0.5 + ux * bow
    return sx, sy, ex, ey, cx, cy
end

-- self-loop on a state circle: a teardrop cubic whose rim points sit at
-- `spread` radians either side of angle `dir` (radians, 0 = +x axis,
-- -pi/2 = top).  `lift` scales how far the loop bulges out (in node
-- radii).  Returns x0,y0, c1x,c1y, c2x,c2y, x1,y1 plus the apex point
-- for the label.
function geo.loop_geom(cx, cy, r, dir, spread, lift)
    dir = dir or -math.pi * 0.5
    spread = spread or 0.55
    lift = lift or 2.2
    local x0 = cx + math.cos(dir - spread) * r
    local y0 = cy + math.sin(dir - spread) * r
    local x1 = cx + math.cos(dir + spread) * r
    local y1 = cy + math.sin(dir + spread) * r
    -- control points pushed out along the rim normals, distance ~ lift*r
    local c1x = cx + math.cos(dir - spread) * r * lift
    local c1y = cy + math.sin(dir - spread) * r * lift
    local c2x = cx + math.cos(dir + spread) * r * lift
    local c2y = cy + math.sin(dir + spread) * r * lift
    return x0, y0, c1x, c1y, c2x, c2y, x1, y1,
           cx + math.cos(dir) * r * (lift - 0.55),
           cy + math.sin(dir) * r * (lift - 0.55)
end

return geo
