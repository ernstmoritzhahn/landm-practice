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
local meta_el    = document:getElementById("meta")
local tree_el    = document.getElementById("tree")
local errline_el = document.getElementById("errline")
local suggest_el = document.getElementById("suggest")

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
    -- LaTeX commands (safe: no member is a prefix of another —
    -- \to, \la, \up, \down are deliberately excluded so \top,
    -- \land, \uparrow, \downarrow remain typeable; the parser still
    -- accepts them and the render shows the symbol)
    {"\\neg", "¬"}, {"\\lnot", "¬"},
    {"\\wedge", "∧"}, {"\\land", "∧"},
    {"\\vee", "∨"}, {"\\lor", "∨"},
    {"\\rightarrow", "→"}, {"\\ra", "→"},
    {"\\leftarrow", "←"}, {"\\gets", "←"},
    {"\\leftrightarrow", "↔"}, {"\\lra", "↔"}, {"\\iff", "↔"},
    {"\\oplus", "⊕"}, {"\\xor", "⊕"},
    {"\\uparrow", "↑"}, {"\\nand", "↑"},
    {"\\downarrow", "↓"}, {"\\nor", "↓"},
    {"\\forall", "∀"}, {"\\exists", "∃"},
    {"\\top", "⊤"}, {"\\bot", "⊥"},
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

-- all input symbols are BMP codepoints: UTF-16 units (the DOM
-- selection API's unit) equal character counts — byte math only has
-- to step over UTF-8 continuation bytes.
local function byte_pos(s, units)
    local i, n = 1, 0
    while i <= #s and n < units do
        local b = s:byte(i)
        i = i + (b < 0x80 and 1 or b < 0xE0 and 2
                 or b < 0xF0 and 3 or 4)
        n = n + 1
    end
    return i - 1
end

local function ulen(s)
    local n = 0
    for i = 1, #s do
        local b = s:byte(i)
        if b < 0x80 or b >= 0xC0 then n = n + 1 end
    end
    return n
end

local alive = false   -- worker answered at least once

local function send_parse()
    local sel = input.selectionStart or #input.value
    util.js_post_message(json.encode(
        {what = "parse", input = input.value,
         prefix = input.value:sub(1, byte_pos(input.value, sel))}))
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
-- caret moves change the continuation vocabulary
input:addEventListener("keyup", send_parse)
input:addEventListener("click", send_parse)

-- symbol buttons insert at the caret
local buttons = document.querySelectorAll(".symbtn")
for i = 0, buttons.length - 1 do
    local b = buttons[i]
    b:addEventListener("click", function()
        local s = b.textContent
        local sel = input.selectionStart or #input.value
        local selEnd = input.selectionEnd or sel
        local v = input.value
        input.value = v:sub(1, byte_pos(v, sel)) .. s ..
                      v:sub(byte_pos(v, selEnd) + 1)
        local pos = sel + 1
        input.selectionStart = pos
        input.selectionEnd = pos
        input:focus()
        send_parse()
    end)
end

local function esc(s)
    return (s:gsub("&", "&amp;"):gsub("<", "&lt;"):gsub(">", "&gt;"))
end

local KIND_COLOR = {op = "#000000", quant = "#0033a0",
                    atom = "#555555", const = "#888888"}

local SVG_PAD = 8   -- viewBox margin so node strokes aren't clipped

local function build_svg(layout)
    local w, h = layout.w + 2 * SVG_PAD, layout.h + 2 * SVG_PAD
    local parts = {'<svg width="' .. w .. '" height="' .. h ..
                   '" viewBox="' .. -SVG_PAD .. ' ' .. -SVG_PAD ..
                   ' ' .. w .. ' ' .. h .. '">'}
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

local function render_suggestions(list)
    local parts = {}
    for _, s in ipairs(list or {}) do
        parts[#parts + 1] =
            '<button class="sugbtn" data-ins="' .. esc(s.ins) ..
            '" data-back="' .. (s.back or 0) .. '">' ..
            esc(s.label or s.ins) .. "</button>"
    end
    suggest_el.innerHTML = table.concat(parts, " ")
    local btns = suggest_el:querySelectorAll(".sugbtn")
    for i = 0, btns.length - 1 do
        local b = btns[i]
        b:addEventListener("click", function()
            local ins = b:getAttribute("data-ins")
            local back = tonumber(b:getAttribute("data-back")) or 0
            local sel = input.selectionStart or #input.value
            local selEnd = input.selectionEnd or sel
            local v = input.value
            input.value = v:sub(1, byte_pos(v, sel)) .. ins ..
                          v:sub(byte_pos(v, selEnd) + 1)
            local pos = sel + ulen(ins) - back
            input.selectionStart = pos
            input.selectionEnd = pos
            input:focus()
            send_parse()
        end)
    end
end

return function(data)
    alive = true
    local msg = json.decode(data)
    render_suggestions(msg.suggestions)
    if msg.ok then
        status_el.textContent = "✓ formula"
        status_el.className = "status ok"
        errline_el.textContent = ""
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
