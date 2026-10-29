-- ui/aut/history.lua -- undo/redo for the automaton editor: a
-- snapshot history over model.to_table/model.load.  model.on_changed
-- fires once per user step (add/remove, toggle, label edit, finished
-- drag), so each stack entry restores exactly one action.  Snapshots
-- are compared via their JSON encoding, so edits outside the model
-- (check toggles, selections) never reach the stack.

local model = require "ui.aut.model"
local json  = require "json"

local H = { max = 200 }

local undo_st, redo_st = {}, {}
local last_snap, last_j = nil, nil
local suppress = false          -- model.load during undo/redo

local function encoded(G) return json.encode(model.to_table(G)) end

-- to be called once, after model.on_changed's other subscribers are
-- wired: records every model change as an undo step
function H.wire(G)
    local prev = model.on_changed
    model.on_changed = function()
        if not suppress then
            local j = encoded(G)
            if j ~= last_j then
                if last_j then
                    undo_st[#undo_st + 1] = last_snap
                    if #undo_st > H.max then
                        table.remove(undo_st, 1)
                    end
                end
                last_snap = model.to_table(G)
                last_j = j
                redo_st = {}
            end
        end
        if prev then prev(G) end
    end
end

-- a fresh task or a restored answer starts an empty history
function H.reset(G)
    undo_st, redo_st = {}, {}
    last_snap = model.to_table(G)
    last_j = encoded(G)
end

local function restore(G, t)
    suppress = true
    model.load(G, t)
    suppress = false
end

function H.can_undo() return #undo_st > 0 end
function H.can_redo() return #redo_st > 0 end

function H.undo(G)
    if #undo_st == 0 then return false end
    redo_st[#redo_st + 1] = last_snap
    last_snap = undo_st[#undo_st]
    undo_st[#undo_st] = nil
    last_j = json.encode(last_snap)
    restore(G, last_snap)
    return true
end

function H.redo(G)
    if #redo_st == 0 then return false end
    undo_st[#undo_st + 1] = last_snap
    last_snap = redo_st[#redo_st]
    redo_st[#redo_st] = nil
    last_j = json.encode(last_snap)
    restore(G, last_snap)
    return true
end

return H
