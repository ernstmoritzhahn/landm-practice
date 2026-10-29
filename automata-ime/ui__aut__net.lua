-- ui/aut/net.lua -- the automaton editor's server link: the same
-- 4-byte big-endian length-prefixed JSON protocol the BayesL client
-- uses (ui/net.lua), trimmed to what this tool needs — the model is
-- pushed on every change plus every check-config edit, the reply is
-- {method="report", seq, problems=[...]} which apply_report maps onto
-- G.prob_nodes/G.prob_edges + message lists for the canvas and the
-- properties column.  seq guards against stale replies.

local ffi   = require "ffi"
local A     = require "ui.api"
local gen   = require "ui.gen"
local G     = require "ui.aut.state"
local model = require "ui.aut.model"
local hist  = require "ui.aut.history"

local json = require "json"    -- resolves via the shared demo path

local NKL = gen.NKL

local net = {}
net.NET = {buf = "", outq = {}, dirty = true, seq = 0,
           asked_model = false, want_model = false}
local NET = net.NET
local netbuf = ffi.new("char[16384]")

-- A.net_send is single-shot nonblocking; a frame must never leave
-- partially, so unsent bytes queue in outq (same discipline as
-- ui/net.lua's NET.flush)
function NET.flush()
    while #NET.outq > 0 do
        local head = NET.outq[1]
        local sent = A.net_send(head, #head)
        if sent == #head then
            table.remove(NET.outq, 1)
        elseif sent > 0 then
            NET.outq[1] = head:sub(sent + 1)
            break
        else
            break
        end
    end
end

local function send(obj)
    if A.net_state() ~= NKL.NET_UP then return end
    local s = json.encode(obj)
    NET.outq[#NET.outq + 1] = string.char(
        math.floor(#s / 16777216) % 256,
        math.floor(#s / 65536) % 256,
        math.floor(#s / 256) % 256,
        #s % 256) .. s
end

-- model or check-config changed -> revalidate (called via
-- model.on_changed and by the panel's toggles/edits)
function net.dirty() NET.dirty = true end

-- index the report for drawing + messages, BayesL apply_report style:
-- worst severity per state/edge id, per-target message lists
local function apply_report(problems)
    G.problems  = {}
    G.prob_nodes = {}
    G.prob_edges = {}
    G.prob_msgs  = {}   -- state id     -> {sev,msg} list
    G.edge_msgs  = {}   -- transition id -> {sev,msg} list
    local errs = 0
    for _, p in ipairs(problems or {}) do
        local sev = (p.sev == "error") and "error" or "warning"
        G.problems[#G.problems + 1] = p
        if sev == "error" then errs = errs + 1 end
        local nid, eid = tonumber(p.node), tonumber(p.edge)
        if nid then
            if sev == "error" or not G.prob_nodes[nid] then
                G.prob_nodes[nid] = sev
            end
            local l = G.prob_msgs[nid]
            if not l then l = {}; G.prob_msgs[nid] = l end
            l[#l + 1] = {sev = sev, msg = tostring(p.msg or p.key)}
        end
        if eid then
            if sev == "error" or not G.prob_edges[eid] then
                G.prob_edges[eid] = sev
            end
            local l = G.edge_msgs[eid]
            if not l then l = {}; G.edge_msgs[eid] = l end
            l[#l + 1] = {sev = sev, msg = tostring(p.msg or p.key)}
        end
    end
    G.model_ok = (errs == 0)
end

local function handle(obj)
    if obj.method == "report" then
        if obj.seq == NET.seq then         -- drop stale replies
            apply_report(obj.problems)
        end
    elseif obj.method == "model" then
        NET.asked_model = true
        if NET.want_model and type(obj.model) == "table" then
            model.load(G, obj.model)
            hist.reset(G)                 -- synced state is the baseline
            NET.dirty = true              -- report the loaded model
        end
        NET.want_model = false
    end
end

function net.poll()
    if A.net_state() ~= NKL.NET_UP then
        -- reconnect state: resend everything once the link is back
        NET.asked_model = false
        NET.dirty = true
        return
    end
    while true do
        local n = A.net_recv(netbuf, 16384)
        if n <= 0 then break end
        NET.buf = NET.buf .. ffi.string(netbuf, n)
    end
    while #NET.buf >= 4 do
        local a, b, c, d = NET.buf:byte(1, 4)
        local len = a * 16777216 + b * 65536 + c * 256 + d
        if #NET.buf < 4 + len then break end
        local payload = NET.buf:sub(5, 4 + len)
        NET.buf = NET.buf:sub(5 + len)
        local ok, obj = pcall(json.decode, payload)
        if ok and type(obj) == "table" then handle(obj) end
    end
    if NET.want_model and not NET.asked_model then
        send{method = "get_model"}
        NET.asked_model = true
    end
    if NET.dirty then
        NET.seq = NET.seq + 1
        send{method = "report", seq = NET.seq,
             model = model.to_table(G), checks = G.checks}
        NET.dirty = false
    end
    NET.flush()
end

return net
