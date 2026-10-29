-- ui/aut/model.lua -- the automaton editor's graph model: states and
-- labelled directed transitions in plain JSON-compatible Lua tables
-- (numbers/strings/booleans only — no ffi).  Self-transitions and
-- parallel transitions are both legal; the multi-label-per-edge
-- question is deferred (a label is a string, "a,b" spellings remain
-- possible at the serialization seam).

local M = {}
M.on_changed = nil     -- optional dirty/model-changed hook

local function changed(G)
    G.nodes_ver = G.nodes_ver + 1
    if M.on_changed then M.on_changed(G) end
end

function M.find_state(G, id)
    for i, n in ipairs(G.nodes) do
        if n.id == id then return i end
    end
    return nil
end

-- first free q<i> name
local function next_name(G)
    local taken = {}
    for _, n in ipairs(G.nodes) do taken[n.name] = true end
    local i = 0
    while taken["q" .. i] do i = i + 1 end
    return "q" .. i
end

function M.add_state(G, x, y)
    local n = {id = G.next_id, x = x, y = y, name = next_name(G),
               -- the first state created is the initial one
               initial = (#G.nodes == 0), accepting = false}
    G.next_id = G.next_id + 1
    G.nodes[#G.nodes + 1] = n
    changed(G)
    return #G.nodes
end

-- returns the edge index, or nil when an endpoint id is unknown
function M.add_transition(G, from, to, label)
    if not M.find_state(G, from) or not M.find_state(G, to) then
        return nil
    end
    G.edges[#G.edges + 1] = {id = G.next_edge_id, from = from, to = to,
                             label = label or ""}
    G.next_edge_id = G.next_edge_id + 1
    changed(G)
    return #G.edges
end

function M.remove_state(G, i)
    if G.nodes[i].locked then return false end  -- given component
    local id = G.nodes[i].id
    table.remove(G.nodes, i)
    -- transitions touching the state go with it
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
    if G.edges[i].locked then return false end  -- given component
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
-- a single undo entry).  Locked (given) states and edges survive; a
-- locked edge whose endpoint was editable dies with its state.
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

-- exactly one initial state; setting it clears the others
function M.set_initial(G, i)
    for j, n in ipairs(G.nodes) do n.initial = (j == i) end
    changed(G)
end

function M.toggle_accepting(G, i)
    G.nodes[i].accepting = not G.nodes[i].accepting
    changed(G)
end

-- JSON shape: {type="nfa", states=[{id,name,x,y,initial,accepting}],
--              transitions=[{id,from,to,label}]}
function M.to_table(G)
    local states, transitions = {}, {}
    for _, n in ipairs(G.nodes) do
        states[#states + 1] = {id = n.id, name = n.name,
                               x = n.x, y = n.y,
                               initial = n.initial and true or false,
                               accepting = n.accepting and true or false,
                               locked = n.locked or nil,
                               seed = n.seed,
                               seed_entry = n.seed_entry or nil,
                               seed_exit = n.seed_exit or nil}
    end
    for _, e in ipairs(G.edges) do
        transitions[#transitions + 1] = {id = e.id, from = e.from,
                                         to = e.to, label = e.label,
                                         locked = e.locked or nil,
                                         seed = e.seed}
    end
    return {type = G.aut_type or "nfa", alphabet = G.alphabet or "",
            stack_alphabet = G.stack_alphabet or "",
            mode = G.mode or "aut", regex = G.regex or "",
            states = states, transitions = transitions}
end

function M.load(G, t)
    G.nodes, G.edges = {}, {}
    G.aut_type = t.type or "nfa"
    -- older snapshots carried {type="dfa", partial=true}: the type
    -- string now encodes the incomplete variant
    if G.aut_type == "dfa" and t.partial then
        G.aut_type = "dfa-part"
    end
    G.alphabet = t.alphabet or ""
    G.stack_alphabet = t.stack_alphabet or ""
    G.mode = t.mode or "aut"
    G.regex = t.regex or ""
    G.next_id, G.next_edge_id = 1, 1
    for _, s in ipairs(t.states or {}) do
        G.nodes[#G.nodes + 1] = {
            id = s.id, x = s.x or 0, y = s.y or 0,
            name = s.name or ("q" .. s.id),
            initial = s.initial and true or false,
            accepting = s.accepting and true or false,
            locked = s.locked and true or nil,
            seed = s.seed,
            seed_entry = s.seed_entry and true or nil,
            seed_exit = s.seed_exit and true or nil}
        if s.id >= G.next_id then G.next_id = s.id + 1 end
    end
    for _, e in ipairs(t.transitions or {}) do
        G.edges[#G.edges + 1] = {id = e.id, from = e.from, to = e.to,
                                 label = e.label or "",
                                 locked = e.locked and true or nil,
                                 seed = e.seed}
        if e.id >= G.next_edge_id then G.next_edge_id = e.id + 1 end
    end
    G.selected, G.sel_edge = nil, nil
    G.hovered, G.hov_edge, G.hov_edge_prev = nil, nil, nil
    G.connecting, G.dragging = nil, nil
    if G.destack then G.destack() end   -- unstack overlapping states
    changed(G)
    return true
end

return M
