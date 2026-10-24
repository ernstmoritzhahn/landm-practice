-- proof_worker.lua — worker side of the induction-proof practice page.
-- Receives JSON from the GUI, answers via util.js_post_message(json).
--
--   {what="tasks"}                     -> {sheets=[sheet structure]}
--   {what="view", id}                  -> {view=tasks.view(task)}
--   {what="check", id, ih, sections}   -> {res=check.check(task, input)}
--
-- data.sections is a dense array of {si=<section index>, ...} so the
-- GUI may omit entirely-empty free-mode blocks.
-- Skeleton input:  sections[].rows[j] may carry {hole="student text"} —
-- the worker fills the task's template holes.  Free input carries
-- {expr="...", cite="..."} rows plus optional section.bind_str.

local util = require "lib.util"
util.fix_path()
local json = require "lib.json"
local T = require "wordproof.term"
local C = require "wordproof.check"
local tasks = require "wordproof.tasks"

local function build_input(task, data)
    local input = { ih = data.ih, sections = {} }
    if task.free then
        for _,sec in ipairs(data.sections or {}) do
            local rows = {}
            for ri,row in ipairs(sec.rows or {}) do
                rows[ri] = { expr = row.expr, cite = row.cite }
            end
            input.sections[sec.si] = { bind_str = sec.bind_str, rows = rows }
        end
        return input
    end
    -- skeleton: fill declared holes
    local by_si = {}
    for _,sec in ipairs(data.sections or {}) do by_si[sec.si] = sec end
    for si,sec in ipairs(task.sections or {}) do
        local rows = {}
        local inrows = (by_si[si] and by_si[si].rows) or {}
        for ri,row in ipairs(sec.rows) do
            local hole = inrows[ri] and inrows[ri].hole
            if row.fixed or not (row.tmpl and row.tmpl:find("?",1,true)) then
                rows[ri] = { expr_parsed = row.tmpl_parsed, cite = row.cite }
            elseif hole == nil or hole == "" then
                rows[ri] = { expr_parsed = row.tmpl_parsed, cite = row.cite }
            else
                local ok,ht = pcall(T.parse, hole, task.spec)
                if ok then
                    rows[ri] = { expr_parsed = T.fill_hole(row.tmpl_parsed, ht),
                                 cite = row.cite }
                else
                    -- let check() produce the parse diagnostic on the raw text
                    rows[ri] = { expr = hole, cite = row.cite }
                end
            end
        end
        input.sections[si] = { rows = rows }
    end
    return input
end

local function send_tasks()
    util.js_post_message(json.encode(
        { what="tasks", sheets=tasks.sheet_structure() }))
end

-- In the worker, prepare() wires js_post_message before this module is
-- required, and worker->gui messages are serialized behind the in-flight
-- require — so pushing the task list here is race-free (the GUI must not
-- post at load time; its bridge is only wired afterwards).
send_tasks()

return function(data)
    local ok,msg = pcall(json.decode, data)
    if not ok then return end
    data = msg
    if data.what == "tasks" then
        send_tasks()
    elseif data.what == "view" then
        local task = tasks.tasks[data.id]
        if task then
            util.js_post_message(json.encode(
                { what="view", id=data.id, view=tasks.view(task) }))
        end
    elseif data.what == "check" then
        local task = tasks.tasks[data.id]
        if not task then return end
        local ok2,input = pcall(build_input, task, data)
        if not ok2 then
            util.js_post_message(json.encode(
                { what="result", id=data.id,
                  res={ ok=false,
                        msg="cannot read input: "..tostring(input) } }))
            return
        end
        local ok3,res = pcall(C.check, task, input)
        if not ok3 then
            res = { ok=false, msg="internal error: "..tostring(res) }
        end
        -- json.encode rejects sparse integer-keyed maps, and res.sections
        -- may skip indices (free mode omits empty sections) — re-serialise
        -- as a dense array carrying si explicitly.
        local secs = {}
        if res.sections then
            local sis = {}
            for si in pairs(res.sections) do sis[#sis+1] = si end
            table.sort(sis)
            for _,si in ipairs(sis) do
                res.sections[si].si = si
                secs[#secs+1] = res.sections[si]
            end
        end
        res.sections = secs
        util.js_post_message(json.encode(
            { what="result", id=data.id, res=res }))
    end
end
