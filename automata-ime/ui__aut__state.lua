-- ui/aut/state.lua -- the automaton editor's widget state: a lean
-- graphw-compatible G.  States live in G.nodes ({id,x,y,name(string),
-- initial,accepting}), transitions in G.edges ({id,from,to,label}).
-- Same field convention as ui/state.lua so the shared skeleton and the
-- tools stay interchangeable.

local ffi = require "ffi"

local G = {
    NODE_R    = 22.0,   -- state radius
    NODE_C    = 7.0,    -- connect-target disc (drawn)
    CONNECT_R = 12.0,   -- connect hit target inside the state
    DRAG_TH   = 4.0,
    EDGE_HIT  = 9.0,
    HOV_HYST  = 4.0,
    nodes = {},          -- states (kept under the generic name)
    edges = {},          -- transitions (ditto)
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
    cv_scroll = ffi.new("unsigned int[2]"),  -- aut canvas viewport
    pm_scroll = ffi.new("unsigned int[2]"),  -- properties column
    split_frac = nil,   -- canvas share of the split row (lazy 0.78)
    split_drag = nil,
    -- task configuration (serialised into model.to_table and pushed
    -- to the consistency server on every change).  mode selects the
    -- object under test: "aut" = the automaton, "re" = the regular
    -- expression in G.regex
    mode     = "aut",
    aut_type = "nfa",   -- nfa|nfa-eps|dfa|dfa-part|pda|tm|tm-N
    alphabet = "",      -- declared alphabet, "" = unspecified
    stack_alphabet = "",-- PDA only: declared stack alphabet
    regex    = "",      -- regular expression source (re mode)
    re_word  = "",      -- scratch word tested against the expression
    checks   = nil,     -- key -> bool toggles (lazy: checks.defaults())
    re_scroll = ffi.new("unsigned int[2]"),  -- re syntax-tree viewport
    -- consistency report applied by ui/aut/net.lua
    problems   = {},
    prob_nodes = nil,   -- state id      -> "error" | "warning"
    prob_edges = nil,   -- transition id -> "error" | "warning"
    prob_msgs  = nil,   -- state id      -> {sev,msg} list
    edge_msgs  = nil,   -- transition id -> {sev,msg} list
    model_ok   = true,  -- false once a report holds an error
}

return G
