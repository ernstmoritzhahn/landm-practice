-- ui/bdd/state.lua -- the BDD editor's widget state: a lean
-- graphw-compatible G.  Decision/terminal nodes live in G.nodes
-- ({id,x,y,label,terminal}), branches in G.edges
-- ({id,from,to,low} — low=true draws the else/false branch dotted,
-- else the then/true branch is drawn solid).  Same field convention
-- as ui/aut/state.lua so the shared skeleton stays interchangeable.

local ffi = require "ffi"

local G = {
    NODE_HW   = 20.0,   -- nonterminal node half-width (min)
    NODE_HH   = 13.0,   -- node half-height
    NODE_R    = 22.0,   -- nominal radius for graphw's circular tests
                        -- (hover hysteresis, label margin, drag clamp);
                        -- precise hits go through ops.hit_node's rects
    NODE_C    = 7.0,    -- connect-target disc (drawn)
    CONNECT_R = 12.0,   -- connect hit target inside the node
    DRAG_TH   = 4.0,
    EDGE_HIT  = 9.0,
    HOV_HYST  = 4.0,
    GRID      = 33.0,   -- node snap quantum
    nodes = {},          -- nodes (kept under the generic name)
    edges = {},          -- branches (ditto)
    nodes_ver = 0,
    next_id = 1,
    next_edge_id = 1,
    selected = nil,      -- index into nodes
    sel_edge = nil,      -- index into edges
    hov_edge = nil,
    hov_edge_prev = nil,
    hovered = nil,
    hover_ctx = nil,
    hover_key = nil,
    dragging = nil,
    drag_dx = 0, drag_dy = 0, drag_moved = false,
    connecting = nil,
    press_x = nil, press_y = nil,
    canvas = {x = 0, y = 0, w = 0, h = 0, vx = 0, vy = 0, vw = 0, vh = 0,
              ox = 0, oy = 0},
    panel  = {x = 0, y = 0, w = 0, h = 0},
    anchor_x = nil, anchor_y = nil,
    view_extent = nil,
    label_epoch = 0,
    cv_scroll = ffi.new("unsigned int[2]"),  -- bdd canvas viewport
    pm_scroll = ffi.new("unsigned int[2]"),  -- properties column
    split_frac = nil,   -- canvas share of the split row (lazy 0.78)
    split_drag = nil,
    -- lightweight local validity hints, recomputed per draw pass:
    -- node id -> "error" | "warning", edge id -> ditto, plus messages
    prob_nodes = nil,
    prob_edges = nil,
}

return G
