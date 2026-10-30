-- ui/bdd/panel.lua -- the BDD editor's property column content:
-- "Node" (kind toggle nonterminal/terminal, label — variable name or
-- terminal value — delete) for G.selected and "Edge" (true/false
-- branch, delete) for G.sel_edge.  Plain rows inside the right-hand
-- group of bdd.frame's split, same idiom as the automaton panel.

local ffi   = require "ffi"
local A     = require "ui.api"
local util  = require "ui.util"
local gen   = require "ui.gen"
local G     = require "ui.bdd.state"
local model = require "ui.bdd.model"
local hist  = require "ui.bdd.history"

local set_str = util.set_str
local NK = gen.NK

local label_buf = ffi.new("char[64]")
local panel_for = nil      -- node id the buffer currently mirrors

local panel = {}

local function changed()
    if model.on_changed then model.on_changed() end
end

local function edit_field(buf, max)
    local ev = A.edit_zt(NK.EDIT_FIELD |
                         (G.readonly and NK.EDIT_READ_ONLY or 0),
                         buf, max)
    if util.hasflag(ev, NK.EDIT_ACTIVE) then G.edit_seen = true end
    return ev
end

local function node_panel()
    local n = G.nodes[G.selected]
    if not n then G.selected = nil return end
    if panel_for ~= n.id then
        panel_for = n.id
        set_str(label_buf, n.label or "")
    end
    A.row(20, 1)
    A.label(n.note and "Annotation"
            or (n.terminal and "Terminal node" or "Decision node"),
            NK.TEXT_LEFT)
    if not n.locked then
        -- kind toggle: decision node (variable), terminal (T/F) or
        -- free annotation text (for step captions)
        A.row(24, 3)
        if A.button("nonterminal") ~= 0 and not G.readonly then
            if n.terminal or n.note then
                n.terminal, n.note = false, nil
                if n.label == "T" or n.label == "F" then
                    n.label = ""
                    set_str(label_buf, "")
                end
                changed()
            end
        end
        if A.button("terminal") ~= 0 and not G.readonly then
            if not n.terminal or n.note then
                n.terminal, n.note = true, nil
                if n.label ~= "T" and n.label ~= "F" then
                    n.label = "T"
                    set_str(label_buf, "T")
                end
                changed()
            end
        end
        if A.button("note") ~= 0 and not G.readonly then
            if not n.note then
                n.note, n.terminal = true, false
                if n.label == "T" or n.label == "F" then
                    n.label = ""
                    set_str(label_buf, "")
                end
                changed()
            end
        end
    end
    A.row(20, 1)
    A.label(n.note and "Text"
            or (n.terminal and "Value" or "Variable"), NK.TEXT_LEFT)
    if n.terminal then
        -- the lecture's vocabulary is T/F: quick buttons plus the
        -- free field (custom values stay possible)
        A.row(24, 2)
        if A.button("T") ~= 0 and not G.readonly and n.label ~= "T" then
            n.label = "T"; set_str(label_buf, "T"); changed()
        end
        if A.button("F") ~= 0 and not G.readonly and n.label ~= "F" then
            n.label = "F"; set_str(label_buf, "F"); changed()
        end
    end
    A.row(26, 1); edit_field(label_buf, 63)
    local nm = ffi.string(label_buf)
    if nm ~= n.label and (nm ~= "" or n.label ~= "?") then
        n.label = nm
        G.nodes_ver = G.nodes_ver + 1
        changed()
    end
    A.row(24, 2)
    if A.button("Delete") ~= 0 and not G.readonly and not n.locked then
        local i = G.selected
        G.selected = nil
        model.remove_node(G, i)
        return
    end
    if A.button("Close") ~= 0 then
        G.selected = nil
    end
end

local function edge_panel()
    local e = G.edges[G.sel_edge]
    if not e then G.sel_edge = nil return end
    local a, b = model.find_node(G, e.from), model.find_node(G, e.to)
    if not (a and b) then G.sel_edge = nil return end
    A.row(20, 1); A.label("Edge", NK.TEXT_LEFT)
    A.row(20, 1)
    A.label(string.format("%s \226\134\146 %s",
            G.nodes[a].label ~= "" and G.nodes[a].label or "?",
            G.nodes[b].label ~= "" and G.nodes[b].label or "?"),
            NK.TEXT_LEFT)
    if not e.locked then
        A.row(24, 1)
        if A.button(e.low and "solid (true)" or "[ solid (true) ]")
           ~= 0 and not G.readonly then
            e.low = false; changed()
        end
        A.row(24, 1)
        if A.button(e.low and "[ dotted (false) ]" or "dotted (false)")
           ~= 0 and not G.readonly then
            e.low = true; changed()
        end
    end
    A.row(24, 2)
    if A.button("Delete") ~= 0 and not G.readonly and not e.locked then
        local i = G.sel_edge
        G.sel_edge = nil
        model.remove_edge(G, i)
        return
    end
    if A.button("Close") ~= 0 then
        G.sel_edge = nil
    end
end

function panel.draw()
    if G.selected then node_panel()
    elseif G.sel_edge then edge_panel()
    else
        A.row(20, 1); A.label("BDD", NK.TEXT_LEFT)
        A.row(20, 1)
        A.label("click empty space to add a node", NK.TEXT_LEFT)
        A.row(20, 1)
        A.label("select a node or edge for options", NK.TEXT_LEFT)
        if hist.undo_depth and hist.undo_depth() > 0 then
            A.row(24, 1)
            if A.button("Undo") ~= 0 then hist.undo(G) end
        end
        if hist.redo_depth and hist.redo_depth() > 0 then
            A.row(24, 1)
            if A.button("Redo") ~= 0 then hist.redo(G) end
        end
    end
end

return panel
