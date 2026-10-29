-- ui/sugbar.lua -- the suggestion button bar shared between the BayesL
-- formula editor and the automata-ime regex workspace: token buttons
-- packed into width-proportional rows, syntax-class tinted via
-- syn.palette, a narrow red delete-token key first.  Layout and
-- colouring live here verbatim; the insert semantics stay with the
-- caller's on_click(item) so each tool keeps its own splice rules.
--
-- Items are plain token strings OR tables {label=, tok=, cls=, del=,
-- del_caret=} — a string equals its label; .del/.del_caret (or the
-- DEL marker string) paints the red delete-token slot; .cls picks a
-- syn.palette class, else opts.classify(label) is asked.

local ffi  = require "ffi"
local A    = require "ui.api"
local gen  = require "ui.gen"
local util = require "ui.util"
local syn  = require "ui.suggest".syn

local NK = gen.NK
local sugbar = {}

sugbar.DEL = "\xE2\x8C\xAB"    -- "⌫" delete-token marker (was DEL_TOK)

local delf4 = ffi.new("float[4]")  -- internal bounds scratch for dbg

local function label_of(it)
    local l = it
    if type(it) == "table" then l = it.label or it.tok end
    return (tostring(l or ""):match("^%s*(.-)%s*$"))
end

local function is_del(it)
    if type(it) == "table" then return it.del or it.del_caret end
    return it == sugbar.DEL
end

-- the share a button wants: measured label + 16 px padding, min 24
local function want_w(it)
    local tw = A.text_width and A.text_width(label_of(it), -1)
    return math.max(24, (tw or 8 * #label_of(it)) + 16)
end

-- Greedy packing into rows that fit cap_px; afterwards the tail is
-- pulled forward so the last row is not a thin leftover (a lone
-- button looks broken — order is preserved).
function sugbar.pack(items, cap_px)
    local rows, row, row_w = {}, {}, 0
    for _, it in ipairs(items) do
        local w = want_w(it)
        local need = w + (#row > 0 and 4 or 0)
        if #row > 0 and row_w + need > cap_px then
            rows[#rows + 1] = row
            row, row_w, need = {}, 0, w
        end
        row[#row + 1] = it
        row_w = row_w + need
    end
    if #row > 0 then rows[#rows + 1] = row end
    local function row_w_of(r)
        local w = 0
        for j, it in ipairs(r) do
            w = w + want_w(it) + (j > 1 and 4 or 0)
        end
        return w
    end
    while #rows >= 2 do
        local last, prev = rows[#rows], rows[#rows - 1]
        -- prev keeps >= 2 buttons, so no new lone row appears
        if #prev < 3 or row_w_of(last) * 2 >= row_w_of(prev) then
            break
        end
        if row_w_of(last) + 4 + want_w(prev[#prev]) > cap_px then
            break
        end
        table.insert(last, 1, table.remove(prev))
    end
    return rows
end

local DEL_COL = {{255, 242, 242}, {255, 214, 214}, {245, 185, 185},
                 {200, 40, 40}, {200, 40, 40}}

local function emit_one(it, classify, plain)
    local lab = label_of(it)
    if is_del(it) then
        if not A.button_col then return A.button(lab) ~= 0 end
        return A.button_col(lab, util.pk(DEL_COL[1]),
                            util.pk(DEL_COL[2]), util.pk(DEL_COL[3]),
                            util.pk(DEL_COL[4]), util.pk(DEL_COL[5]))
               ~= 0
    end
    -- plain rows (the soft-keyboard char rows) stay untinted — only
    -- the dbg class hook still records what the key would be
    local cls = type(it) == "table" and it.cls
    if not cls and classify then cls = classify(lab) end
    local pal = not plain and cls and syn.palette[cls]
    if pal and A.button_col then
        return A.button_col(lab, util.pk(pal.bg), util.pk(pal.hov),
                            util.pk(pal.act), util.pk(pal.fg),
                            util.pk(pal.bor)) ~= 0
    end
    return A.button(lab) ~= 0
end

-- Emit one packed row at the current cursor position: DYNAMIC layout,
-- each button's share proportional to its measured width; a leading
-- delete key keeps a narrow share.  opts:
--   w_px      available width in px (sizes the narrow del share)
--   h         row height
--   classify  fn(label) -> syn class name (for items without .cls)
--   on_click  fn(it)    — clicked items dispatch here
--   dbg       {first=f4, rects=t, labels=t, classes=t} — browser test
--             hooks: per-button bounds/labels/classes, first gets the
--             FIRST emitted button's bounds (set dbg.got_first to skip)
function sugbar.emit_row(row, opts)
    local tw, total = {}, 0
    for j, it in ipairs(row) do
        tw[j] = want_w(it)
        total = total + tw[j]
    end
    local del_r = 0
    if #row > 0 and is_del(row[1]) then
        del_r = math.min(0.25, (tw[1] + 6) / math.max(1, opts.w_px))
    end
    local rest = total - (del_r > 0 and tw[1] or 0)
    local lone = del_r > 0 and #row == 1
    A.row_begin(NK.DYNAMIC, opts.h, #row + (lone and 1 or 0))
    local used = 0
    local dbg = opts.dbg
    for j, it in ipairs(row) do
        local r
        if j == 1 and del_r > 0 then
            r = del_r
            used = used + r
        elseif j < #row then
            r = rest > 0 and tw[j] / rest * (1 - del_r) or 0.0001
            used = used + r
        else
            r = math.max(0.0001, 1.0 - used)
        end
        A.row_push(r)
        if dbg then
            A.widget_bounds(delf4)
            if dbg.first and not dbg.got_first then
                dbg.got_first = true
                A.widget_bounds(dbg.first)
            end
            if dbg.rects then
                dbg.rects[#dbg.rects + 1] = {x = delf4[0], y = delf4[1],
                                             w = delf4[2], h = delf4[3]}
            end
            dbg.n = (dbg.n or 0) + 1
            local idx = dbg.n
            -- labels keep the raw token (boundary padding like " IN"
            -- included) — the browser tests match against it
            if dbg.labels then
                dbg.labels[idx] = type(it) == "table"
                                  and (it.tok or it.label) or it
            end
            if dbg.classes then
                local cls = type(it) == "table" and it.cls
                if not cls and opts.classify then
                    cls = opts.classify(label_of(it))
                end
                dbg.classes[idx] = cls or "default"
            end
        end
        if emit_one(it, opts.classify, opts.plain) and opts.on_click then
            opts.on_click(it)
        end
    end
    if lone then
        A.row_push(math.max(0.0001, 1.0 - used))
        A.label("", NK.TEXT_LEFT)
    end
    A.row_end()
end

return sugbar
