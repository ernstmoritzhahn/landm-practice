-- Formula-input demonstrator GUI (main thread).
-- Follows html/grammar_gui.lua: DOM via util.js bridges, requests go
-- to html/logic_worker through util.js_post_message.

local util = require "lib.util"
local json = require "lib.json"

util.fix_path()

local window = util.js_get("window")
local document = window.document

local input      = document:getElementById("formula")
local status_el  = document:getElementById("status")
local render_el  = document:getElementById("render")
local meta_el    = document:getElementById("meta")
local tree_el    = document:getElementById("tree")
local errline_el = document:getElementById("errline")

-- ASCII digraphs live-replaced by their Unicode connectives.
-- Ordered: multi-char before the overlaps they would otherwise eat
-- (typed '<' '-' '>' first becomes '<-' then '←', and the trailing '>'
-- merges via the '←>' entry).
local replacements = {
    {"<->", "↔"}, {"<=>", "↔"}, {"==", "↔"},
    {"->", "→"}, {"=>", "→"},
    {"<-", "←"}, {"<=", "←"},
    {"←>", "↔"}, {"←=", "↔"}, {"→<", "↔"}, {"=<","↔"},
    {"&&", "∧"}, {"/\\", "∧"},
    {"||", "∨"}, {"\\/", "∨"},
    {"~", "¬"}, {"!", "¬"},
}
-- escape pattern-magic characters once
for _, r in ipairs(replacements) do
    r.pat = (r[1]:gsub("(%W)", "%%%1"))
end

local function replace_symbols(element)
    local sel = element.selectionStart
    for _, r in ipairs(replacements) do
        local count
        element.value, count = element.value:gsub(r.pat, r[2])
        if count > 0 and sel > 0 then
            -- selectionStart is a UTF-16 index: every ASCII digraph
            -- and every replacement symbol is exactly 1 unit
            sel = math.max(0, sel - count * (#r[1] - 1))
            element.selectionStart = sel
            element.selectionEnd = sel
        end
    end
end

local alive = false   -- worker answered at least once

local function send_parse()
    util.js_post_message(json.encode(
        {what = "parse", input = input.value}))
end

-- util_worker drops messages that arrive before its module is loaded:
-- keep resending the current input until the first reply comes back.
local function retry_until_alive()
    if alive then return end
    send_parse()
    window:setTimeout(retry_until_alive, 500)
end
window:setTimeout(retry_until_alive, 500)

input:addEventListener("input", function()
    replace_symbols(input)
    send_parse()
end)

-- symbol buttons insert at the caret
local buttons = document.querySelectorAll(".symbtn")
for i = 0, buttons.length - 1 do
    local b = buttons[i]
    b:addEventListener("click", function()
        local s = b.textContent
        local sel = input.selectionStart or #input.value
        input.value = input.value:sub(1, sel) .. s ..
                      input.value:sub(sel + 1)
        input.selectionStart = sel + 1
        input.selectionEnd = sel + 1
        input:focus()
        send_parse()
    end)
end

local function esc(s)
    return (s:gsub("&", "&amp;"):gsub("<", "&lt;"):gsub(">", "&gt;"))
end

local KIND_COLOR = {op = "#000000", quant = "#0033a0",
                    atom = "#555555", const = "#888888"}

local function build_svg(layout)
    local w, h = layout.w, layout.h
    local parts = {'<svg width="' .. w .. '" height="' .. h ..
                   '" viewBox="0 0 ' .. w .. ' ' .. h .. '">'}
    local function nd(id) return layout.nodes[id] end
    for _, e in ipairs(layout.edges) do
        local a, b = nd(e.from), nd(e.to)
        parts[#parts + 1] =
            '<line x1="' .. a.x .. '" y1="' .. (a.y + a.h / 2) ..
            '" x2="' .. b.x .. '" y2="' .. (b.y - b.h / 2) ..
            '" stroke="#ccc" stroke-width="1.5"/>'
    end
    for _, n in ipairs(layout.nodes) do
        local col = KIND_COLOR[n.kind] or "#000"
        parts[#parts + 1] =
            '<rect x="' .. (n.x - n.w / 2) .. '" y="' .. (n.y - n.h / 2)
            .. '" width="' .. n.w .. '" height="' .. n.h
            .. '" rx="4" fill="#fff" stroke="' .. col
            .. '" stroke-width="1.5"/>'
        parts[#parts + 1] =
            '<text x="' .. n.x .. '" y="' .. (n.y + 5)
            .. '" text-anchor="middle" font-size="14" fill="' .. col
            .. '">' .. esc(n.label) .. '</text>'
    end
    parts[#parts + 1] = "</svg>"
    return table.concat(parts)
end

local function chip(text, cls)
    return '<span class="chip ' .. (cls or "") .. '">' ..
           esc(text) .. "</span>"
end

return function(data)
    alive = true
    local msg = json.decode(data)
    if msg.ok then
        status_el.textContent = "✓ formula"
        status_el.className = "status ok"
        errline_el.textContent = ""
        render_el.textContent = msg.render
        local chips = {chip(msg.kind)}
        chips[#chips + 1] = chip(msg.closed and "closed" or "open")
        for _, v in ipairs(msg.free or {}) do
            chips[#chips + 1] = chip("free: " .. v, "var")
        end
        meta_el.innerHTML = table.concat(chips)
        tree_el.innerHTML = build_svg(msg.layout)
    else
        status_el.textContent = "✗ " .. msg.message
        status_el.className = "status err"
        render_el.textContent = ""
        meta_el.innerHTML = ""
        tree_el.innerHTML = ""
        -- caret display: byte-accurate slice (error positions are at
        -- token starts)
        local pos = msg.pos or 1
        local pre  = esc(input.value:sub(1, pos - 1))
        local mark = esc(input.value:sub(pos, pos))
        local post = esc(input.value:sub(pos + 1))
        errline_el.innerHTML =
            '<pre class="errline">' .. pre ..
            '<span class="caret">' .. (mark ~= "" and mark or " ")
            .. "</span>" .. post .. "</pre>"
    end
end
