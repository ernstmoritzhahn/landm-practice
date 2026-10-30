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

-- ---- task/answer hooks --------------------------------------------
-- One <bdd-app> = one diagram; multi-step questions place several
-- elements in the sub-exercise body with author-typed headers between
-- them, so the editor itself carries no step titles.  The task JSON
-- (the exam's @@ block) may still preset a starting model via
-- {initial = {<model>}}; answers serialise as
-- {type="bdd", nodes, edges}.

function ui_task(payload)
    local ok, t = pcall(json_mod.decode, payload or "")
    if not ok or type(t) ~= "table" then return end
    -- a task payload means exam context
    G.exam = true
    -- a prefill (task.initial) restores the starting answer without
    -- counting as a student edit
    _suppress_dirty = true
    if type(t.initial) == "table" then
        model.load(G, t.initial)
    else
        model.load(G, {})
    end
    _suppress_dirty = false
    hist.reset(G)
end

-- Anubis contract: "" means unanswered
function ui_get_state()
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
    -- legacy multi-step payload: keep the first diagram
    if type(t.steps) == "table" and type(t.steps[1]) == "table" then
        t = {type = "bdd", nodes = t.steps[1].nodes,
             edges = t.steps[1].edges}
    end
    _suppress_dirty = true
    model.load(G, t)
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
