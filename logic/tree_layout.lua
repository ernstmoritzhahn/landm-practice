-- Render a logic/syntax.lua formula AST as a tree layout.
-- Adapted from bayesian_networks/artifact-ifs-site/logic/tree_layout.lua:
-- pure-Lua Buchheim–Jünger–Leipert tidy-tree packing producing a
-- JSON-friendly {nodes, edges, w, h} the client draws.
--
-- Formula-tree convention: atoms are leaves (rendered with their term
-- arguments), op nodes carry the connective symbol, quantifier nodes
-- carry "∀x"/"∃x" with the body below.

local formula = require "logic.formula"

local tree = {}

tree.NODE_MIN_W  = 26
tree.NODE_H      = 26
tree.NODE_X_GAP  = 14
tree.NODE_Y_GAP  = 26
tree.NODE_CHAR_W = 9

local OP_SYM = {}
for k, v in pairs(require "logic.operators".by_key) do
    OP_SYM[k] = v.default_symbol
end

local function node_label(f)
    if f.type == "op" then
        return OP_SYM[f.op] or f.op
    elseif f.type == "quant" then
        local vs = {}
        for i, v in ipairs(f.vars) do vs[i] = v.name end
        return (f.quant == "forall" and "∀" or "∃")
            .. table.concat(vs, ",")
    elseif f.type == "atom" then
        if #f.args == 0 then return f.name end
        return formula.render(f)
    elseif f.type == "true" then
        return "⊤"
    elseif f.type == "false" then
        return "⊥"
    end
    return "?"
end

local function node_kind(f)
    if f.type == "op" then return "op" end
    if f.type == "quant" then return "quant" end
    if f.type == "atom" then return "atom" end
    return "const"
end

local function children_of(f)
    if f.type == "op" then
        return f.args
    elseif f.type == "quant" then
        return {f.body}
    end
    return {}
end

local function build_tree(f, nodes, edges, parent_id)
    local id = #nodes + 1
    local n = {
        id = id,
        label = node_label(f),
        kind = node_kind(f),
        from = f.pos and f.pos.from or 0,
        to = f.pos and f.pos.to or 0,
        children = {},
    }
    nodes[id] = n
    if parent_id then
        edges[#edges + 1] = {from = parent_id, to = id}
        nodes[parent_id].children[#nodes[parent_id].children + 1] = id
    end
    for _, c in ipairs(children_of(f)) do
        build_tree(c, nodes, edges, id)
    end
    return id
end

-- Buchheim–Jünger–Leipert tidy layout (verbatim port of the BN one;
-- deterministic — same AST, same geometry)
local function layout_tidy(nodes, root_id)
    for _, n in ipairs(nodes) do
        n.h = tree.NODE_H
        n.w = math.max(tree.NODE_MIN_W, #n.label * tree.NODE_CHAR_W + 10)
    end

    local sibNo, lSib, par = {}, {}, {}
    for _, n in ipairs(nodes) do
        for i, cid in ipairs(n.children) do
            sibNo[cid] = i
            lSib[cid] = n.children[i - 1]
            par[cid] = n.id
        end
    end
    local function lmost(id)
        while lSib[id] do id = lSib[id] end
        return id
    end
    local function dist(a, b)
        return nodes[a].w / 2 + tree.NODE_X_GAP + nodes[b].w / 2
    end

    local prelim, mod, anc, thr = {}, {}, {}, {}
    local shift_, change_ = {}, {}
    local function nextLeft(id)  return thr[id] or nodes[id].children[1] end
    local function nextRight(id)
        local c = nodes[id].children
        return thr[id] or c[#c]
    end
    local function moveSubtree(wm, wp, shift)
        local subtrees = sibNo[wp] - sibNo[wm]
        change_[wp] = (change_[wp] or 0) - shift / subtrees
        shift_[wp]  = (shift_[wp]  or 0) + shift
        change_[wm] = (change_[wm] or 0) + shift / subtrees
        prelim[wp]  = prelim[wp] + shift
        mod[wp]     = (mod[wp] or 0) + shift
    end
    local function executeShifts(v)
        local shift, change = 0, 0
        local ch = nodes[v].children
        for i = #ch, 1, -1 do
            local w = ch[i]
            prelim[w] = prelim[w] + shift
            mod[w] = (mod[w] or 0) + shift
            change = change + (change_[w] or 0)
            shift = shift + (shift_[w] or 0) + change
        end
    end
    local apportion
    local function firstWalk(v)
        anc[v] = v
        prelim[v] = 0
        local l = lSib[v]
        local ch = nodes[v].children
        if #ch == 0 then
            if l then prelim[v] = prelim[l] + dist(l, v) end
            return
        end
        local defaultAncestor = ch[1]
        for _, w in ipairs(ch) do
            firstWalk(w)
            defaultAncestor = apportion(w, defaultAncestor)
        end
        executeShifts(v)
        local mid = (prelim[ch[1]] + prelim[ch[#ch]]) / 2
        if l then
            prelim[v] = prelim[l] + dist(l, v)
            mod[v] = prelim[v] - mid
        else
            prelim[v] = mid
        end
    end
    function apportion(v, defaultAncestor)
        local w = lSib[v]
        if not w then return defaultAncestor end
        local vip, vop, vim = v, v, w
        local vom = lmost(vip)
        local sip = mod[vip] or 0
        local sop = mod[vop] or 0
        local sim = mod[vim] or 0
        local som = mod[vom] or 0
        while nextRight(vim) and nextLeft(vip) do
            vim = nextRight(vim); vip = nextLeft(vip)
            vom = nextLeft(vom); vop = nextRight(vop)
            anc[vop] = v
            local shift = (sim + prelim[vim])
                        - (sip + prelim[vip]) + dist(vim, vip)
            if shift > 0 then
                local wm = anc[vim]
                if par[wm] ~= par[v] then wm = defaultAncestor end
                moveSubtree(wm, v, shift)
                sip = sip + shift; sop = sop + shift
            end
            sim = sim + (mod[vim] or 0); sip = sip + (mod[vip] or 0)
            som = som + (mod[vom] or 0); sop = sop + (mod[vop] or 0)
        end
        if nextRight(vim) and not nextRight(vop) then
            thr[vop] = nextRight(vim)
            sop = sop + (mod[vop] or 0)
            mod[vop] = sop + (mod[vim] or 0) - (mod[vop] or 0)
        end
        if nextLeft(vip) and not nextLeft(vim) then
            thr[vim] = nextLeft(vip)
            sim = sim + (mod[vim] or 0)
            mod[vim] = sim + (mod[vip] or 0) - (mod[vim] or 0)
        end
        return defaultAncestor
    end
    firstWalk(root_id)
    local function secondWalk(v, m, depth)
        n = nodes[v]
        n.x = prelim[v] + m
        n.y = depth * (tree.NODE_H + tree.NODE_Y_GAP)
        for _, w in ipairs(n.children) do
            secondWalk(w, m + (mod[v] or 0), depth + 1)
        end
    end
    secondWalk(root_id, 0, 0)

    local min_left, max_right, max_bottom = math.huge, -math.huge, 0
    for _, n in ipairs(nodes) do
        local l = n.x - n.w / 2
        local r = n.x + n.w / 2
        if l < min_left then min_left = l end
        if r > max_right then max_right = r end
        if n.y + n.h > max_bottom then max_bottom = n.y + n.h end
    end
    for _, n in ipairs(nodes) do
        n.x = n.x - min_left + 4
        n.y = n.y + 4
    end
    return max_right - min_left + 8, max_bottom + 8
end

-- tree.layout(ast) -> {nodes, edges, w, h, root}
function tree.layout(f)
    local nodes, edges = {}, {}
    local root = build_tree(f, nodes, edges, nil)
    local w, h = layout_tidy(nodes, root)
    return {nodes = nodes, edges = edges, w = w, h = h, root = root}
end

return tree
