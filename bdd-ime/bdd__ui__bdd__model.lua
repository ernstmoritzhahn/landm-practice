-- ui/bdd/model.lua -- the BDD editor's graph model: decision and
-- terminal nodes plus low/high branches in plain JSON-compatible Lua
-- tables (numbers/strings/booleans only — no ffi).  A BDD is a DAG,
-- but the model itself is permissive (the canvas flags anomalies —
-- cycles, a terminal with children, more than two branches — instead
-- of forbidding them: students may draw intermediate stages too).
--
-- Node: {id,x,y,label,terminal} — label is the variable for decision
-- nodes, "T"/"F" (or free text) for terminals.
-- Edge: {id,from,to,low} — low=true is the else/false branch
-- (dotted), else the then/true branch (solid).

local M = {}
M.on_changed = nil     -- optional dirty/model-changed hook

local function changed(G)
    G.nodes_ver = G.nodes_ver + 1
    if M.on_changed then M.on_changed(G) end
end

function M.find_node(G, id)
    for i, n in ipairs(G.nodes) do
        if n.id == id then return i end
    end
    return nil
end

function M.add_node(G, x, y)
    local n = {id = G.next_id, x = x, y = y, label = "",
               terminal = false}
    G.next_id = G.next_id + 1
    G.nodes[#G.nodes + 1] = n
    changed(G)
    return #G.nodes
end

-- default branch kind for a new edge from_id -> to_id: leftward drops
-- read as the else/low branch, rightward as then/high (the lecture's
-- convention); when the source already carries that kind the new one
-- defaults to the other so a node's second branch differs from its
-- first without any clicking.
local function default_low(G, from_id, to_id)
    local fi, ti = M.find_node(G, from_id), M.find_node(G, to_id)
    if not (fi and ti) then return false end
    local a, b = G.nodes[fi], G.nodes[ti]
    local low = (b.x < a.x)
    for _, e in ipairs(G.edges) do
        if e.from == from_id then
            if e.low == low then low = not low end
            break
        end
    end
    return low
end

-- returns the edge index, or nil when an endpoint id is unknown
function M.add_edge(G, from, to, low)
    if not M.find_node(G, from) or not M.find_node(G, to) then
        return nil
    end
    if low == nil then low = default_low(G, from, to) end
    G.edges[#G.edges + 1] = {id = G.next_edge_id, from = from, to = to,
                             low = low and true or false}
    G.next_edge_id = G.next_edge_id + 1
    changed(G)
    return #G.edges
end

function M.remove_node(G, i)
    if G.nodes[i].locked then return false end  -- given component
    local id = G.nodes[i].id
    table.remove(G.nodes, i)
    for j = #G.edges, 1, -1 do
        local e = G.edges[j]
        if e.from == id or e.to == id then table.remove(G.edges, j) end
    end
    if G.selected == i then G.selected = nil
    elseif G.selected and G.selected > i then G.selected = G.selected - 1 end
    if G.hovered == i then G.hovered = nil
    elseif G.hovered and G.hovered > i then G.hovered = G.hovered - 1 end
    changed(G)
end

function M.remove_edge(G, i)
    if G.edges[i].locked then return false end
    table.remove(G.edges, i)
    if G.sel_edge == i then G.sel_edge = nil
    elseif G.sel_edge and G.sel_edge > i then
        G.sel_edge = G.sel_edge - 1
    end
    if G.hov_edge == i then G.hov_edge = nil end
    if G.hov_edge_prev == i then G.hov_edge_prev = nil end
    changed(G)
end

-- wipe every editable component in ONE step (single changed() call ->
-- a single undo entry).  Locked (given) elements survive.
function M.clear(G)
    local alive = {}
    for _, n in ipairs(G.nodes) do
        if n.locked then alive[n.id] = true end
    end
    local nn, ne, removed = {}, {}, false
    for _, n in ipairs(G.nodes) do
        if n.locked then nn[#nn + 1] = n else removed = true end
    end
    for _, e in ipairs(G.edges) do
        if e.locked and alive[e.from] and alive[e.to] then
            ne[#ne + 1] = e
        else
            removed = true
        end
    end
    if not removed then return end
    G.nodes, G.edges = nn, ne
    G.selected, G.sel_edge = nil, nil
    G.hovered, G.hov_edge, G.hov_edge_prev = nil, nil, nil
    changed(G)
end

-- roots: per weakly connected component, the node without incoming
-- edges (ties: topmost-leftmost).  Computed — the student never marks
-- a root; direction is implicit top-to-bottom.
function M.roots(G)
    local has_in, adj = {}, {}
    for _, e in ipairs(G.edges) do
        has_in[e.to] = true
        adj[e.from] = adj[e.from] or {}
        adj[e.from][#adj[e.from] + 1] = e.to
        adj[e.to] = adj[e.to] or {}
        adj[e.to][#adj[e.to] + 1] = e.from
    end
    local by_id = {}
    for i, n in ipairs(G.nodes) do by_id[n.id] = i end
    local seen, roots = {}, {}
    -- annotation nodes never participate in a component
    for _, n in ipairs(G.nodes) do
        if n.note then seen[n.id] = true end
    end
    for i, n in ipairs(G.nodes) do
        if not seen[n.id] then
            -- flood the component
            local comp, stack = {}, {n.id}
            seen[n.id] = true
            while #stack > 0 do
                local id = table.remove(stack)
                comp[#comp + 1] = id
                for _, m in ipairs(adj[id] or {}) do
                    if not seen[m] then seen[m] = true
                        stack[#stack + 1] = m end
                end
            end
            -- component root: a source if present, else topmost node
            local best
            for _, id in ipairs(comp) do
                local k = by_id[id]
                local cn = G.nodes[k]
                local cand = (not has_in[id]) and 0 or 1
                if not best or cand < best.c
                   or (cand == best.c and
                       (cn.y < best.y or
                        (cn.y == best.y and cn.x < best.x))) then
                    best = {i = k, c = cand, x = cn.x, y = cn.y}
                end
            end
            if best then roots[#roots + 1] = best.i end
        end
    end
    return roots
end

-- JSON shape: {type="bdd",
--   nodes=[{id,x,y,label,terminal}],
--   edges=[{id,from,to,low}]}
function M.to_table(G)
    local nodes, edges = {}, {}
    for _, n in ipairs(G.nodes) do
        nodes[#nodes + 1] = {id = n.id, x = n.x, y = n.y,
                             label = n.label or "",
                             terminal = n.terminal and true or false,
                             note = n.note and true or nil,
                             locked = n.locked or nil}
    end
    for _, e in ipairs(G.edges) do
        edges[#edges + 1] = {id = e.id, from = e.from, to = e.to,
                             low = e.low and true or false,
                             locked = e.locked or nil}
    end
    return {type = "bdd", nodes = nodes, edges = edges}
end

function M.load(G, t)
    G.nodes, G.edges = {}, {}
    G.next_id, G.next_edge_id = 1, 1
    for _, s in ipairs(t.nodes or {}) do
        G.nodes[#G.nodes + 1] = {
            id = s.id, x = s.x or 0, y = s.y or 0,
            label = s.label or "",
            terminal = s.terminal and true or false,
            note = s.note and true or nil,
            locked = s.locked and true or nil}
        if s.id >= G.next_id then G.next_id = s.id + 1 end
    end
    for _, e in ipairs(t.edges or {}) do
        G.edges[#G.edges + 1] = {id = e.id, from = e.from, to = e.to,
                                 low = e.low and true or false,
                                 locked = e.locked and true or nil}
        if e.id >= G.next_edge_id then G.next_edge_id = e.id + 1 end
    end
    G.selected, G.sel_edge = nil, nil
    G.hovered, G.hov_edge, G.hov_edge_prev = nil, nil, nil
    G.connecting, G.dragging = nil, nil
    if G.destack then G.destack() end
    changed(G)
    return true
end

return M
