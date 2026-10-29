-- automata-ime/ui.lua — entry point of the standalone automaton
-- editor.  The C frontend (main.c + nkl.c, compiled from
-- ../nuklear-ime-demo) loads THIS file and drives it through the same
-- ui_set_api / ui_parse_args / ui_frame hooks as the BN demonstrator.
--
-- Module resolution: this directory first (ui/aut/*, this file's
-- siblings), then ../nuklear-ime-demo for the SHARED modules
-- (ui.api, ui.util, ui.geom, ui.graphw, ui.gen, ui.args).  Keep the
-- split that way: tool-specific code here, generic infrastructure in
-- the demo tree — one source of truth, no copies.

local _src = debug.getinfo(1, "S").source or ""
local _dir = _src:sub(1, 1) == "@"
             and (_src:sub(2):match("^(.*)[/\\]") or ".") or "."
local SHARED = _dir .. "/../../bayesian_networks/nuklear-ime-demo"
-- teaching/lua holds the shared automaton label grammars
-- (automata.label_lang) used by the typed-label checks
local TEACHING = _dir .. "/../../teaching/lua"
package.path  = _dir .. "/?.lua;" .. SHARED .. "/?.lua;" ..
                TEACHING .. "/?.lua;" .. package.path
package.cpath = package.cpath .. ";" ..
                SHARED .. "/../build/lpeg-1.1.0/?.so;" ..
                SHARED .. "/../build/lpeg-1.0.2/?.so"

-- the nkl_api cdef must be registered before ui_set_api() casts the
-- bridge pointer — gen.lua only ships the string, cdef'ing is the
-- entry file's job (same as the demonstrator's ui.lua)
local ffi = require "ffi"
ffi.cdef(require("ui.gen").cdef)

local api_mod  = require "ui.api"
local args_mod = require "ui.args"
local aut      = require "ui.aut"
local autnet   = require "ui.aut.net"
local G        = require "ui.aut.state"
local model    = require "ui.aut.model"
local checks   = require "server.checks"

-- every check enabled by default; the properties column toggles
-- entries off individually — the same table goes to the server
G.checks = checks.defaults()
-- standalone sessions may always simulate; task payloads opt in via
-- t.sim (practice site sets it, Anubis exams omit it)
G.sim_enabled = true
model.on_changed = autnet.dirty

-- browser loopback: the web bnNet shim calls nkl_lua_service, which
-- invokes this global — the same request dispatch the standalone
-- server/service.lua runs, answered inside this Lua state instead of
-- a spawned server or worker.  Unused under the native build.
package.preload["checks"] = function() return require "server.checks" end
local _svc = require("server.service").new(require "json")
function ui_service(payload) return _svc(payload) end

-- shared main.c drops the #bnload overlay once
-- ui_query("ui_model_ready()") answers "1" (15 s deadline otherwise);
-- this app has no remote model fetch, it is ready on first frame
function ui_query(expr)
    if expr == "ui_model_ready()" then return "1" end
    -- dev/test probe: evaluate "return <expr>" with G and api in scope
    local loader = loadstring or load
    if not loader then return "no-loader" end
    local fn, cerr = loader("local G, api_mod = ... return " .. tostring(expr))
    if not fn then return "load-err:" .. tostring(cerr) end
    local ok, v = pcall(fn, G, api_mod)
    if not ok then return "run-err:" .. tostring(v) end
    return tostring(v)
end

-- ---- Anubis-plugin hooks (web build only) --------------------------
-- The <automata-app> element drives these through the nkl_lua_*
-- exports; natively nothing calls them.  Task JSON (the exam's @@
-- block) presets the editor; the answer is model.to_table's JSON;
-- ui_dirty counts student edits so the element can emit
-- sendDataToExternal; G.readonly freezes all mutation paths for
-- review mode.
local _dirty_n = 0
local _suppress_dirty = false   -- programmatic loads are not edits
local _on_changed = model.on_changed
model.on_changed = function()
    if not _suppress_dirty then _dirty_n = _dirty_n + 1 end
    if _on_changed then _on_changed() end
end

local json_mod = require "json"
local checks_mod = require "server.checks"
local hist = require "ui.aut.history"
hist.wire(G)        -- wraps model.on_changed: every edit is an undo step
hist.reset(G)

function ui_task(payload)
    local ok, t = pcall(json_mod.decode, payload or "")
    if not ok or type(t) ~= "table" then return end
    -- a task payload means exam context: the question author fixed
    -- mode/type/alphabet/checks, so the panel must not offer them
    G.exam = true
    if t.mode == "re" or t.mode == "aut" then G.mode = t.mode end
    if type(t.alphabet) == "string" then G.alphabet = t.alphabet end
    if type(t.stack_alphabet) == "string" then
        G.stack_alphabet = t.stack_alphabet
    end
    if type(t.aut_type) == "string"
       and (checks_mod.is_known_type
            and checks_mod.is_known_type(t.aut_type)
            or t.aut_type == "dfa" or t.aut_type == "dfa-part"
            or t.aut_type == "nfa" or t.aut_type == "nfa-eps") then
        G.aut_type = t.aut_type
    end
    -- checks are opt-in in exams: off unless the task enables them
    -- (the standalone default is all-on for exploration).  A task may
    -- also ask for an EDITABLE checks bar (checks_editable): then every
    -- check defaults ON — t.checks[key]==false is an explicit opt-out —
    -- and the panel offers per-check toggles plus an all-on/off button.
    -- Exam deployments simply omit the flag.
    G.checks_editable = (t.checks_editable == true)
    -- the word simulator is a practice-site feature: the task opts in
    -- (Anubis questions never set the flag)
    G.sim_enabled = (t.sim == true)
    G.sim, G.sim_live, G.sim_edges = nil, nil, nil
    G.checks = {}
    for _, s in ipairs(checks_mod.specs) do
        local v = type(t.checks) == "table" and t.checks[s.key]
        if v == nil then v = G.checks_editable end
        G.checks[s.key] = (v == true)
    end
    -- a prefill (task.initial) restores a starting answer without
    -- counting as a student edit
    if type(t.initial) == "table" then
        _suppress_dirty = true
        model.load(G, t.initial)
        _suppress_dirty = false
    end
    hist.reset(G)   -- a fresh task gets a fresh undo history
    autnet.dirty()
end

-- Anubis contract: "" means unanswered
function ui_get_state()
    local t = model.to_table(G)
    if t.mode == "re" then
        if not (t.regex or ""):find("%S") then return "" end
    elseif not t.states or #t.states == 0 then
        return ""
    end
    return json_mod.encode(t)
end

function ui_load_state(payload)
    local t = {}
    if payload and payload ~= "" then
        local ok, dec = pcall(json_mod.decode, payload)
        if ok and type(dec) == "table" then t = dec end
    end
    _suppress_dirty = true
    model.load(G, t)
    _suppress_dirty = false
    G.sim, G.sim_live, G.sim_edges = nil, nil, nil
    hist.reset(G)   -- a restored answer is the new baseline
end

function ui_readonly(ro)
    -- the C bridge passes a number; 0 in Lua is truthy, so compare
    local on = (ro == true) or (ro == 1) or (ro == "1")
    G.readonly = on
    if api_mod.bayes_readonly then
        api_mod.bayes_readonly(on and 1 or 0)
    end
end

function ui_dirty() return _dirty_n end

-- --model loads an automaton snapshot locally (no server round-trip
-- needed — the file is the client's own automaton JSON)
local model_file = nil

-- AUT_SEED=1 (dev): preload a small automaton with both-direction,
-- parallel and loop edges + labels so NKL_SHOT captures show the real
-- rendering paths without a mouse.
if os.getenv and os.getenv("AUT_SEED") then
    local q0 = model.add_state(G, 132, 198)
    local q1 = model.add_state(G, 396, 198)
    local q2 = model.add_state(G, 594, 330)
    local q3 = model.add_state(G, 726, 132)
    model.add_transition(G, G.nodes[q0].id, G.nodes[q1].id, "a")
    model.add_transition(G, G.nodes[q1].id, G.nodes[q0].id, "b")
    model.add_transition(G, G.nodes[q1].id, G.nodes[q2].id, "c,d")
    model.add_transition(G, G.nodes[q1].id, G.nodes[q2].id, "e")
    model.add_transition(G, G.nodes[q2].id, G.nodes[q2].id, "f")
    model.add_transition(G, G.nodes[q0].id, G.nodes[q0].id, "z")
    model.add_transition(G, G.nodes[q1].id, G.nodes[q3].id, "g")
    -- AUT_SEL=N additionally selects edge N as if clicked; AUT_SELN=N
    -- selects state N
    local sel = tonumber(os.getenv("AUT_SEL") or "")
    if sel then G.sel_edge = sel end
    local seln = tonumber(os.getenv("AUT_SELN") or "")
    if seln then G.selected = seln end
    G.aut_type = os.getenv("AUT_TYPE") or "nfa"
    G.alphabet = os.getenv("AUT_ALPHA") or "a,b,c,d,e,f,g,z"
    -- dev edges for the consistency paths: a lambda transition on
    -- NFA-λ, an explicitly unlabelled one via AUT_EMPTY=1
    if G.aut_type == "nfa-eps" then
        model.add_transition(G, G.nodes[q3].id, G.nodes[q1].id,
                             "\xce\xbb")
    end
    if os.getenv("AUT_EMPTY") then
        model.add_transition(G, G.nodes[q2].id, G.nodes[q1].id, "")
    end
elseif os.getenv and os.getenv("AUT_MINIMAL") then
    local q0 = model.add_state(G, 264, 264)
    local q1 = model.add_state(G, 528, 264)
    if os.getenv("AUT_MINIMAL") == "3" then
        -- dev: three identical 'a' transitions on a DFA — the whole
        -- conflict group should be flagged, not just the surplus
        G.nodes[q0].initial = true
        model.add_transition(G, G.nodes[q0].id, G.nodes[q1].id, "a")
        model.add_transition(G, G.nodes[q0].id, G.nodes[q1].id, "a")
        model.add_transition(G, G.nodes[q0].id, G.nodes[q1].id, "a")
        G.aut_type = "dfa"
        G.alphabet = "a,b"
    elseif os.getenv("AUT_MINIMAL") == "2" then
        -- the 2x2-grid example: straight horizontal/vertical/diagonal
        -- transitions + a loop — exercises label placement
        G.nodes[q0].initial = true
        local q2 = model.add_state(G, 264, 528)
        local q3 = model.add_state(G, 528, 528)
        model.add_transition(G, G.nodes[q0].id, G.nodes[q1].id, "a")
        model.add_transition(G, G.nodes[q0].id, G.nodes[q2].id, "b")
        model.add_transition(G, G.nodes[q2].id, G.nodes[q1].id, "a,b")
        model.add_transition(G, G.nodes[q2].id, G.nodes[q3].id, "a,b")
        model.add_transition(G, G.nodes[q3].id, G.nodes[q1].id, "b")
        model.add_transition(G, G.nodes[q3].id, G.nodes[q3].id, "a")
    else
        -- dev: two states, two unlabelled opposing transitions — the
        -- "empty label" error pair used for arrow-rendering checks
        model.add_transition(G, G.nodes[q0].id, G.nodes[q1].id, "")
        model.add_transition(G, G.nodes[q1].id, G.nodes[q0].id, "")
    end
end

-- AUT_RE='a∪(b·a)*' (dev): start in regular-expression mode with the
-- given source (AUT_ALPHA presets the alphabet, AUT_WORD the test
-- word) — screenshot verification without clicking
if os.getenv and os.getenv("AUT_RE") then
    G.mode = "re"
    G.regex = os.getenv("AUT_RE")
    G.alphabet = os.getenv("AUT_ALPHA") or G.alphabet
    G.re_word = os.getenv("AUT_WORD") or ""
end

-- AUT_SIM="word;steps" (dev): open the Simulate panel pre-stepped —
-- same purpose as AUT_SEED for the simulator's live-state painting
if os.getenv and os.getenv("AUT_SIM") then
    require("ui.aut.sim").dev_run(os.getenv("AUT_SIM"))
end

function ui_set_api(p, hex)
    api_mod.bind(p, hex)
end

-- like the BayesL tool the editor talks to a spawned consistency
-- server (auto-started unless --host/--port connect elsewhere);
-- --model restores an automaton JSON, --features/FONT stay unused
local AUT_CAP = { server = true, port = 9101,
                  features = false, font = false }

function ui_parse_args(argv, desktop)
    local r, err = args_mod.parse(argv, desktop, AUT_CAP)
    if r then model_file = r.model end
    return r, err
end

function ui_usage(prog)
    io.write(string.format(
        "Usage: %s [--host H] [--port P] [--model FILE]\n" ..
        "          [--width W] [--height H] [--fullscreen] [--resizable]\n",
        prog))
    io.write("  --host        connect to consistency server (127.0.0.1)\n")
    io.write("  --port        server TCP port (9101)\n")
    io.write("  --model FILE  restore an automaton snapshot (JSON)\n")
    io.write("  --width       SDL window width in pixels\n")
    io.write("  --height      SDL window height in pixels\n")
    io.write("  --fullscreen  start in fullscreen\n")
    io.write("  --resizable   allow the window to be resized\n")
end

local frame_no = 0

function ui_frame(x, y, w, h, hint)
    frame_no = frame_no + 1
    -- shrink-to-fit on WIDTH only: the UI is laid out for >= 560 wide
    -- and narrower windows scale font and elements down.  Height no
    -- longer participates — a short host is supposed to crop the
    -- canvas (it has scrollbars) rather than shrink the drawing, or
    -- the page's fit-to-content height would just zoom everything out
    -- (reference must match -DNKL_REF_W in the Makefile)
    local s = math.min(1.0, w / 560.0)
    -- AUT_MOUSE="x,y" (dev): pin the pointer so NKL_SHOT captures show
    -- hover states without a mouse
    local fm = os.getenv and os.getenv("AUT_MOUSE")
    if fm then
        local fx, fy = fm:match("(-?%d+),(-?%d+)")
        if fx and api_mod.fake_mouse then
            api_mod.fake_mouse(tonumber(fx), tonumber(fy))
        end
    end
    -- AUT_CLICKS="x,y@f;x,y@f" (dev): fake left clicks — each pair fires
    -- on frame f (press) and releases at frame end.  Window-absolute
    -- logical coords, like AUT_MOUSE.
    local fc = os.getenv and os.getenv("AUT_CLICKS")
    if fc and api_mod.fake_click then
        for c in fc:gmatch("[^;]+") do
            local cx, cy, cf = c:match("(-?%d+),(-?%d+)@(%d+)")
            if cf and tonumber(cf) == frame_no then
                api_mod.fake_click(tonumber(cx), tonumber(cy))
            end
        end
    end
    if model_file then
        -- restore once on the first frame: the file overrides the seed
        local f = io.open(model_file, "r")
        if f then
            local ok, t = pcall(require("json").decode, f:read("*a"))
            f:close()
            if ok and type(t) == "table" then
                model.load(G, t)
                hist.reset(G)
            end
        else
            io.stderr:write("automata-ime: cannot read " .. model_file ..
                            "\n")
        end
        model_file = nil
    end
    autnet.poll()
    return aut.frame(x, y, w, h, s, hint)
end
