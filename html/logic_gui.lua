-- Formula-input demonstrator GUI (main thread).
-- Follows html/grammar_gui.lua: DOM via util.js bridges, requests go
-- to html/logic_worker through util.js_post_message.

local util = require "lib.util"
local json = require "lib.json"
local dom_input = require "html.dom_input"

util.fix_path()

local window = util.js_get("window")
local document = window.document

local fhl_el     = document:getElementById("fhl")
local propchk    = document:getElementById("propchk")
local input      = document:getElementById("formula")
local status_el  = document:getElementById("status")
local meta_el    = document:getElementById("meta")
local tree_el    = document.getElementById("tree")
local suggest_el = document.getElementById("suggest")

-- ASCII digraphs live-replaced by their Unicode connectives.
-- Ordered: multi-char before the overlaps they would otherwise eat
-- (typed '<' '-' '>' first becomes '<-' then '←', and the trailing '>'
-- merges via the '←>' entry).  `find` strings match literally.
local replacements = {
    {find = "<->", to = "↔"}, {find = "<=>", to = "↔"},
    {find = "==", to = "↔"},
    {find = "->", to = "→"}, {find = "=>", to = "→"},
    {find = "<-", to = "←"}, {find = "<=", to = "←"},
    {find = "←>", to = "↔"}, {find = "←=", to = "↔"},
    {find = "→<", to = "↔"}, {find = "=<", to = "↔"},
    {find = "&&", to = "∧"}, {find = "/\\", to = "∧"},
    {find = "||", to = "∨"}, {find = "\\/", to = "∨"},
    {find = "~", to = "¬"}, {find = "!", to = "¬"},
    -- LaTeX commands.  The four boundary-marked ones are prefixes of
    -- longer commands (\to<\top, \la<\land, \up<\uparrow,
    -- \down<\downarrow): they convert only once a non-identifier
    -- byte follows, so the longer spellings stay typeable.
    {find = "\\neg", to = "¬"}, {find = "\\lnot", to = "¬"},
    {find = "\\wedge", to = "∧"}, {find = "\\land", to = "∧"},
    {find = "\\vee", to = "∨"}, {find = "\\lor", to = "∨"},
    {find = "\\rightarrow", to = "→"}, {find = "\\ra", to = "→"},
    {find = "\\implies", to = "→"},
    {find = "\\to", to = "→", boundary = true},
    {find = "\\leftarrow", to = "←"}, {find = "\\gets", to = "←"},
    {find = "\\la", to = "←", boundary = true},
    {find = "\\leftrightarrow", to = "↔"}, {find = "\\lra", to = "↔"},
    {find = "\\Leftrightarrow", to = "↔"},
    {find = "\\iff", to = "↔"},
    {find = "\\oplus", to = "⊕"}, {find = "\\xor", to = "⊕"},
    {find = "\\uparrow", to = "↑"}, {find = "\\nand", to = "↑"},
    {find = "\\up", to = "↑", boundary = true},
    {find = "\\downarrow", to = "↓"}, {find = "\\nor", to = "↓"},
    {find = "\\down", to = "↓", boundary = true},
    {find = "\\forall", to = "∀"}, {find = "\\exists", to = "∃"},
    {find = "\\top", to = "⊤"}, {find = "\\bot", to = "⊥"},
    -- pseudo-LaTeX: intuitive names for students, no real commands
    {find = "\\not", to = "¬"}, {find = "\\and", to = "∧"},
    {find = "\\or", to = "∨"},
    {find = "\\true", to = "⊤"}, {find = "\\false", to = "⊥"},
}

local units_len = dom_input.units_len
local byte_pos = dom_input.byte_pos
local char_bytes = dom_input.char_bytes

local function replace_symbols(element)
    dom_input.replace_symbols(element, replacements)
end

local alive = false   -- worker answered at least once

local function send_parse()
    local sel = input.selectionStart or units_len(input.value)
    util.js_post_message(json.encode(
        {what = "parse", input = input.value,
         prop = propchk.checked,
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
-- keep the painted layer aligned with the field's horizontal scroll
input:addEventListener("scroll", function()
    fhl_el.scrollLeft = input.scrollLeft
end)
propchk:addEventListener("change", send_parse)

-- (no static symbol palette: the suggestion chips offer exactly the
-- continuations that are legal at the caret, and ASCII digraphs /
-- LaTeX commands are normalised to Unicode while typing)

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
            local sel = input.selectionStart or units_len(input.value)
            local selEnd = input.selectionEnd or sel
            local v = input.value
            input.value = v:sub(1, byte_pos(v, sel)) .. ins ..
                          v:sub(byte_pos(v, selEnd) + 1)
            local pos = sel + units_len(ins) - back
            input.selectionStart = pos
            input.selectionEnd = pos
            -- the inserted text may complete a pending command
            -- (\to followed by a symbol converts to →)
            replace_symbols(input)
            input:focus()
            send_parse()
        end)
    end
end

-- errpos (byte offset of a parse error) marks the single offending
-- character inside the field itself — the painted layer sits exactly
-- under the input text, so a highlighted char there reads as the
-- error position without a separate error line
local function paint_spans(spans, errpos)
    local v, parts = input.value, {}
    local marked = false
    for _, s in ipairs(spans or {}) do
        local cls = "hl-" .. s.cls
        if errpos and not marked and s.f <= errpos and errpos < s.t then
            local bl = math.max(char_bytes(v, errpos), 1)
            if s.f < errpos then
                parts[#parts + 1] = '<span class="' .. cls .. '">' ..
                    esc(v:sub(s.f, errpos - 1)) .. "</span>"
            end
            parts[#parts + 1] = '<span class="' .. cls .. ' hl-bad">'
                .. esc(v:sub(errpos, math.min(errpos + bl, s.t) - 1))
                .. "</span>"
            if errpos + bl < s.t then
                parts[#parts + 1] = '<span class="' .. cls .. '">' ..
                    esc(v:sub(errpos + bl, s.t - 1)) .. "</span>"
            end
            marked = true
        else
            parts[#parts + 1] = '<span class="' .. cls .. '">' ..
                esc(v:sub(s.f, s.t - 1)) .. "</span>"
        end
    end
    -- error at end of input: mark a trailing blank
    if errpos and not marked then
        parts[#parts + 1] = '<span class="hl-bad"> </span>'
    end
    fhl_el.innerHTML = table.concat(parts)
end

return function(data)
    alive = true
    local msg = json.decode(data)
    render_suggestions(msg.suggestions)
    -- only paint when the reply describes the current text — a stale
    -- response would misalign the colored layer with the caret
    local fresh = msg.input == input.value
    if msg.ok then
        if fresh then paint_spans(msg.spans) end
        status_el.textContent = "✓ formula"
        status_el.className = "status ok"
        local chips = {chip(msg.kind)}
        chips[#chips + 1] = chip(msg.closed and "closed" or "open")
        for _, v in ipairs(msg.free or {}) do
            chips[#chips + 1] = chip("free: " .. v, "var")
        end
        meta_el.innerHTML = table.concat(chips)
        tree_el.innerHTML = build_svg(msg.layout)
    else
        -- the offending character is marked inside the input field
        -- (byte pos, token-start aligned — paint_spans splits spans)
        if fresh then paint_spans(msg.spans, msg.pos or 1) end
        status_el.textContent = "✗ " .. msg.message
        status_el.className = "status err"
        meta_el.innerHTML = ""
        tree_el.innerHTML = ""
    end
end
