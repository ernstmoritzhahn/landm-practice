-- ui/util.lua — small shared helpers: ffi string/colour packing, flag
-- tests, edit-widget sentinels, rect tests, dashed drawing primitives.
-- Editor state does not live here — that is ui/state.lua (E); this file
-- only holds what every module needs.

local ffi = require "ffi"
local A = require "ui.api"

local util = {}

-- The bridge returns -1 on the desktop and 0xFFFFFFFF in the browser
-- WASM build when no edit widget is active (32-bit sign-extension
-- difference).  Treat both sentinels as "no active edit".
util.EDIT_NONE = 0xFFFFFFFF
function util.edit_is_active(f)
    return f and f >= 0 and f ~= util.EDIT_NONE
end

function util.hasflag(v, f) return math.floor(v / f) % 2 == 1 end

function util.col(c) return c[1], c[2], c[3], c[4] or 255 end

-- pack {r,g,b[,a]} as 0xRRGGBBAA for draw_text (see the cdef note);
-- return a signed int so 0xFF..FF marshals the same under luaffifb
function util.pk(c)
    local v = c[1]*16777216 + c[2]*65536 + c[3]*256 + (c[4] or 255)
    if v >= 2147483648 then v = v - 4294967296 end
    return v
end

util.DASH_ON  = 4.0
util.DASH_OFF = 3.0

function util.dashed_line(canvas, x0, y0, x1, y1, thick, c, on, off)
    on = on or util.DASH_ON
    off = off or util.DASH_OFF
    local dx, dy = x1 - x0, y1 - y0
    local len = math.sqrt(dx * dx + dy * dy)
    if len < 0.5 then return end
    local ux, uy = dx / len, dy / len
    local r, g, b, a = util.col(c)
    local seg = on + off
    local p = 0
    while p < len do
        local s = p + on
        if s > len then s = len end
        local sx = x0 + ux * p
        local sy = y0 + uy * p
        local ex = x0 + ux * s
        local ey = y0 + uy * s
        A.stroke_line(canvas, sx, sy, ex, ey, thick, r, g, b, a)
        p = p + seg
    end
end

function util.dashed_circle(canvas, cx, cy, rad, thick, c)
    local circ = 2 * math.pi * rad
    local seg = util.DASH_ON + util.DASH_OFF
    local n = math.floor(circ / seg)
    if n < 4 then n = 4 end
    local da = 2 * math.pi / n
    local dash_a = util.DASH_ON / rad
    local r, g, b, a = util.col(c)
    for i = 0, n - 1 do
        local a0 = i * da
        local a1 = a0 + dash_a
        if a1 > a0 + da then a1 = a0 + da end
        local x1 = cx + rad * math.cos(a0)
        local y1 = cy + rad * math.sin(a0)
        local x2 = cx + rad * math.cos(a1)
        local y2 = cy + rad * math.sin(a1)
        A.stroke_line(canvas, x1, y1, x2, y2, thick, r, g, b, a)
    end
end

function util.set_str(buf, s)
    local cap = tonumber(ffi.sizeof(buf))
    if not cap or cap < 1 then return end
    if #s == 0 then
        buf[0] = 0
        return
    end
    local n = math.min(#s, cap - 1)
    ffi.copy(buf, s, n)
    buf[n] = 0
end

-- UTF-8 rune count (nuklear's edit cursor counts runes, not bytes)
function util.utf8_len(s)
    local n = 0
    for i = 1, #s do
        local b = s:byte(i)
        if b < 0x80 or b >= 0xC0 then n = n + 1 end
    end
    return n
end

-- Replace every occurrence of plain `tok` by `sym` in s, tracking a
-- cursor given as a rune index into the OLD string.  Returns the new
-- string and the cursor's rune index in it, so the caller can hand it
-- to A.edit_set_cursor() — without the adjustment the widget's stored
-- rune offset points past the shrunken text (caret visually snaps to
-- the field start while input lands at the old offset).
function util.sub_track_cursor(s, cur, tok, sym)
    local out, i, delta = {}, 1, 0
    local sym_r = util.utf8_len(sym)
    while true do
        local a, b = s:find(tok, i, true)
        if not a then break end
        if cur >= 0 then
            local a_run = util.utf8_len(s:sub(1, a - 1))
            local b_run = util.utf8_len(s:sub(1, b))
            if b_run <= cur then
                delta = delta + (b_run - a_run) - sym_r
            elseif a_run < cur then
                -- cursor sits inside the replaced token: land after sym
                delta = delta + (cur - a_run) - sym_r
            end
        end
        out[#out + 1] = s:sub(i, a - 1) .. sym
        i = b + 1
    end
    out[#out + 1] = s:sub(i)
    return table.concat(out), cur - delta
end

function util.clamp(v, lo, hi)
    if v < lo then return lo elseif v > hi then return hi end
    return v
end

function util.in_rect(px, py, r)
    return px >= r.x and px < r.x + r.w and py >= r.y and py < r.y + r.h
end

function util.escape_pattern(s)
    return (s:gsub("([%^%$%(%)%%%.%[%]%*%+%-%?])", "%%%1"))
end


function util.wrap_text(text, max_w)
    if not text or text == "" or max_w <= 0 then
        return ""
    end
    local space_w = A.text_width(" ", 1)
    local lines = {}
    local cur = ""
    local cur_w = 0
    for word in text:gmatch("%S+") do
        local ww = A.text_width(word, -1)
        if cur_w > 0 and cur_w + space_w + ww > max_w then
            lines[#lines + 1] = cur
            cur = word
            cur_w = ww
        else
            if cur_w > 0 then
                cur = cur .. " " .. word
                cur_w = cur_w + space_w + ww
            else
                cur = word
                cur_w = ww
            end
        end
    end
    if cur ~= "" then
        lines[#lines + 1] = cur
    end
    return table.concat(lines, "\n")
end

-- Remove the last token from a BayesL formula string.  Whitespace is
-- trimmed, then the last token (identifier, number, or single-rune
-- operator/punctuation) is dropped.  Multi-byte UTF-8 operators such as
-- ¬, ∧, ≤, ℙ/𝒫, 𝔼/𝕍/σ and □ are handled.

return util
