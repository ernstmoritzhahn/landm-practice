-- bdd-ime/ui.lua — entry point of the BDD editor.  The shared C
-- frontend (main.c + nkl.c, compiled from ../nuklear-ime-demo) loads
-- THIS file and drives it through the same ui_set_api /
-- ui_parse_args / ui_frame hooks as the automaton editor.
--
-- Module resolution: this directory first (ui/bdd/*), then the demo
-- tree for the SHARED modules (ui.api, ui.util, ui.geom, ui.graphw,
-- ui.gen, ui.args).  Tool-specific code here, generic infrastructure
-- in the demo tree — one source of truth, no copies.

local _src = debug.getinfo(1, "S").source or ""
local _dir = _src:sub(1, 1) == "@"
             and (_src:sub(2):match("^(.*)[/\\]") or ".") or "."
local SHARED = _dir .. "/../../bayesian_networks/nuklear-ime-demo"
package.path  = _dir .. "/?.lua;" .. SHARED .. "/?.lua;" ..
                package.path

local ffi = require "ffi"
ffi.cdef(require("ui.gen").cdef)

local api_mod  = require "ui.api"
local args_mod = require "ui.args"
local bdd      = require "ui.bdd"
local G        = require "ui.bdd.state"
local model    = require "ui.bdd.model"
local hist     = require "ui.bdd.history"
local json_mod = require "json"

-- no consistency server in this tool: the canvas validates locally.
-- ui_service stays defined so the ime.js loopback shim (which posts
-- frames only when Lua calls net_send) has a benign answer anyway.
function ui_service(payload) return "{}" end

function ui_query(expr)
    if expr == "ui_model_ready()" then return "1" end
    local loader = loadstring or load
    if not loader then return "no-loader" end
    local fn, cerr = loader("local G, api_mod = ... return "
                            .. tostring(expr))
    if not fn then return "load-err:" .. tostring(cerr) end
    local ok, v = pcall(fn, G, api_mod)
    if not ok then return "run-err:" .. tostring(v) end
    return tostring(v)
end

-- ---- Anubis-plugin hooks (web build only) --------------------------
-- The <bdd-app> element drives these through the nkl_lua_* exports.
-- Task JSON (the exam's @@ block) presets the editor; the answer is
-- model.to_table's JSON; ui_dirty counts student edits so the element
-- can emit sendDataToExternal; G.readonly freezes mutations.
local _dirty_n = 0
local _suppress_dirty = false
model.on_changed = function()
    if not _suppress_dirty then _dirty_n = _dirty_n + 1 end
end

hist.wire(G)
hist.reset(G)

-- ---- multi-diagram tasks ------------------------------------------
-- A task may ask for several diagrams, one per construction step:
--   {steps = {"composition", "merge leaves", "remove spurious q"},
--    initial = {<model> | {<model>, ...}}}
-- The editor keeps ONE live model plus a parked to_table per step;
-- a tab row (drawn by ui/bdd.lua) switches steps.  Answers serialise
-- as {type="bdd_multi", steps=[{caption, ...model}]}; single-diagram
-- tasks stay {type="bdd", nodes, edges}.
G.step_captions, G.step_data, G.step_i = nil, nil, 1

local function step_park()
    if not G.step_captions then return end
    G.step_data[G.step_i] = model.to_table(G)
end

function step_switch(k)
    if not G.step_captions or k == G.step_i
       or k < 1 or k > #G.step_captions then return end
    step_park()
    _suppress_dirty = true
    model.load(G, G.step_data[k] or {})
    _suppress_dirty = false
    G.step_i = k
    hist.reset(G)     -- undo stays per-diagram
end

function ui_task(payload)
    local ok, t = pcall(json_mod.decode, payload or "")
    if not ok or type(t) ~= "table" then return end
    -- a task payload means exam context
    G.exam = true
    G.step_captions, G.step_data, G.step_i = nil, nil, 1
    if type(t.steps) == "table" and #t.steps > 1 then
        G.step_captions = {}
        for i, c in ipairs(t.steps) do
            G.step_captions[i] = tostring(c)
        end
        G.step_data = {}
    end
    -- a prefill (task.initial) restores starting answers without
    -- counting as a student edit; per-step form: {m1, m2, ...}
    _suppress_dirty = true
    if type(t.initial) == "table" then
        if G.step_captions and t.initial[1] ~= nil
           and type(t.initial[1]) == "table" then
            for i, m in ipairs(t.initial) do
                if type(m) == "table" then G.step_data[i] = m end
            end
            model.load(G, G.step_data[1] or {})
        else
            model.load(G, t.initial)
            if G.step_captions then G.step_data[1] = t.initial end
        end
    else
        model.load(G, {})
    end
    _suppress_dirty = false
    hist.reset(G)
end

-- Anubis contract: "" means unanswered
function ui_get_state()
    if G.step_captions then
        step_park()
        local steps, empty = {}, true
        for i, c in ipairs(G.step_captions) do
            local m = G.step_data[i] or
                      {type = "bdd", nodes = {}, edges = {}}
            steps[#steps + 1] = {caption = c, nodes = m.nodes,
                                 edges = m.edges}
            if m.nodes and #m.nodes > 0 then empty = false end
        end
        if empty then return "" end
        return json_mod.encode({type = "bdd_multi", steps = steps})
    end
    local t = model.to_table(G)
    if not t.nodes or #t.nodes == 0 then return "" end
    return json_mod.encode(t)
end

function ui_load_state(payload)
    local t = {}
    if payload and payload ~= "" then
        local ok, dec = pcall(json_mod.decode, payload)
        if ok and type(dec) == "table" then t = dec end
    end
    _suppress_dirty = true
    if type(t.steps) == "table" and G.step_captions then
        G.step_data = {}
        for i, s in ipairs(t.steps) do
            G.step_data[i] = {nodes = s.nodes or {},
                              edges = s.edges or {}}
            if not G.step_captions[i] then
                G.step_captions[i] = s.caption or
                                     ("step " .. i)
            end
        end
        model.load(G, G.step_data[1] or {})
        G.step_i = 1
    else
        model.load(G, t)
    end
    _suppress_dirty = false
    hist.reset(G)
end

function ui_readonly(ro)
    local on = (ro == true) or (ro == 1) or (ro == "1")
    G.readonly = on
    if api_mod.bayes_readonly then
        api_mod.bayes_readonly(on and 1 or 0)
    end
end

function ui_dirty() return _dirty_n end

-- --model restores a BDD snapshot locally
local model_file = nil

-- BDD_SEED=1 (dev): preload the BDD(p) shape + a bigger example so
-- NKL_SHOT captures show the real rendering paths without a mouse
if os.getenv and os.getenv("BDD_SEED") then
    local p  = model.add_node(G, 264, 66)
    local f  = model.add_node(G, 198, 198)
    local t  = model.add_node(G, 330, 198)
    G.nodes[p].label = "p"
    G.nodes[f].label, G.nodes[f].terminal = "F", true
    G.nodes[t].label, G.nodes[t].terminal = "T", true
    model.add_edge(G, G.nodes[p].id, G.nodes[t].id, false)
    model.add_edge(G, G.nodes[p].id, G.nodes[f].id, true)
end

function ui_set_api(p, hex)
    api_mod.bind(p, hex)
end

local BDD_CAP = { server = false, features = false, font = false }

function ui_parse_args(argv, desktop)
    local r, err = args_mod.parse(argv, desktop, BDD_CAP)
    if r then model_file = r.model end
    return r, err
end

function ui_usage(prog)
    io.write(string.format(
        "Usage: %s [--model FILE] [--width W] [--height H] " ..
        "[--fullscreen] [--resizable]\n", prog))
    io.write("  --model FILE  restore a BDD snapshot (JSON)\n")
    io.write("  --width       SDL window width in pixels\n")
    io.write("  --height      SDL window height in pixels\n")
    io.write("  --fullscreen  start in fullscreen\n")
    io.write("  --resizable   allow the window to be resized\n")
end

local frame_no = 0

function ui_frame(x, y, w, h, hint)
    frame_no = frame_no + 1
    local s = math.min(1.0, w / 560.0)
    if model_file then
        local f = io.open(model_file, "r")
        if f then
            local ok, t = pcall(require("json").decode, f:read("*a"))
            f:close()
            if ok and type(t) == "table" then
                model.load(G, t)
                hist.reset(G)
            end
        else
            io.stderr:write("bdd-ime: cannot read " .. model_file
                            .. "\n")
        end
        model_file = nil
    end
    return bdd.frame(x, y, w, h, s, hint)
end
