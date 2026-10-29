-- DOM text-input helpers shared by the html GUIs.
--
-- Lua strings are UTF-8 byte strings, but the DOM selection API
-- (selectionStart/selectionEnd) counts UTF-16 code units: BMP
-- codepoints take 1 unit (1-3 bytes), supplementary codepoints take
-- 2 units (4 bytes).  All text operations (sub, gsub, find) need byte
-- offsets, all selection properties need unit indices — mix them up
-- and carets/highlights drift as soon as a multi-byte symbol is in
-- the field.  These helpers keep the two measures separate.

local M = {}

--- UTF-16 length of a Lua string (what the DOM reports for its text).
function M.units_len(s)
    local n = 0
    for i = 1, #s do
        local b = s:byte(i)
        if b < 0x80 or b >= 0xC0 then
            n = n + (b >= 0xF0 and 2 or 1)
        end
    end
    return n
end

--- byte offset behind the units-th character — i.e. how many bytes
--- text before a DOM index occupies: value:sub(1, byte_pos(v, sel))
--- is exactly the text before the caret.
function M.byte_pos(s, units)
    local i, n = 1, 0
    while i <= #s and n < units do
        local b = s:byte(i)
        i = i + (b < 0x80 and 1 or b < 0xE0 and 2
                 or b < 0xF0 and 3 or 4)
        n = n + (b >= 0xF0 and 2 or 1)
    end
    return i - 1
end

--- byte length of the UTF-8 character starting at byte index i
--- (0 when i is beyond the end of s).
function M.char_bytes(s, i)
    local b = s:byte(i)
    if not b then return 0 end
    return b < 0x80 and 1 or b < 0xE0 and 2 or b < 0xF0 and 3 or 4
end

--- Live symbol replacement for an <input>/<textarea>: rewrites
--- ASCII digraphs / word commands to their Unicode symbols while the
--- user types, keeping the caret where it belongs.
---
--- entries: array of {find = string, to = string, plain = bool?} —
--- find is matched literally unless plain == false (then it is a Lua
--- pattern like gsub's first argument).  List order matters when
--- replacements overlap (run multi-char before the prefixes they eat).
---
--- Only matches that start at or before the caret move the caret —
--- replacing text further right must not shift the selection.
function M.replace_symbols(element, entries)
    local sel = element.selectionStart or M.units_len(element.value)
    for _, e in ipairs(entries) do
        local v = element.value
        local selb = M.byte_pos(v, sel)
        local out, init, moved = {}, 1, 0
        while true do
            local f, t = v:find(e.find, init, e.plain ~= false)
            if not f then break end
            if f <= selb then
                moved = moved + M.units_len(v:sub(f, t))
                              - M.units_len(e.to)
            end
            out[#out + 1] = v:sub(init, f - 1) .. e.to
            init = t + 1 > init and t + 1 or init + 1
        end
        if init > 1 then
            element.value = table.concat(out) .. v:sub(init)
            sel = math.max(0, sel - moved)
            element.selectionStart = sel
            element.selectionEnd = sel
        end
    end
end

return M
