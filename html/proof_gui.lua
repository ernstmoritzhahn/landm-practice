-- proof_gui.lua — main-thread side of the induction-proof practice page.
-- Renders sheet -> exercise-group tabs -> subtask tabs -> variant toggle,
-- loads the task view from the worker, renders the chain editor into
-- #proof, and sends {what="check"} requests.  The returned function is
-- the worker->GUI message handler (cf. html/grammar_gui.lua).

local util = require "lib.util"
local json = require "lib.json"
util.fix_path()

local window = util.js_get("window")
local document = window.document

local function get(id) return document:getElementById(id) end
local checkbtn = get("check")
local tabs_el  = get("tabs")
local subtabs_el = get("subtabs")
local variant_el = get("variant")
local goal_el, ihrow_el = get("goal"), get("ihrow")
local rulesbox_el = get("rulesbox")
local proof_el, summary_el = get("proof"), get("summary")

local state = {
    sheets = nil,          -- tab structure from the worker
    group_i = 1,           -- selected exercise-group tab
    sub_i   = 1,           -- selected subtask tab
    free    = false,       -- variant toggle
    id = nil, view = nil,
    holes = {}, st = {}, free_blocks = {},
}

-- ---------- dom helpers ----------
local function el(tag, cls, html)
    local e = document:createElement(tag)
    if cls then e.className = cls end
    if html then e.innerHTML = html end
    return e
end
local function clear(e) e.innerHTML = "" end
local function text(tag, s, cls)
    local e = el(tag, cls)
    e.textContent = s
    return e
end

-- ---------- input helpers ----------
local replace_table = {
    ["\\lambda"]   = "λ",
    ["\\Sigma"]    = "Σ",
    ["\\sum"]      = "Σ",
    ["\\emptyset"] = "∅",
}
local function replace_symbols(e)
    local sel = e.selectionStart
    for k,v in pairs(replace_table) do
        local count
        e.value, count = e.value:gsub(k, v)
        if count > 0 then
            sel = sel - #k + 1
            e.selectionStart = sel
            e.selectionEnd = sel
        end
    end
end
-- oninput: clear the given status cell + the summary (stale verdicts
-- must not survive edits)
local function mk_input(cls, width, oninput)
    local i = el("input", cls)
    i.type = "text"
    i:setAttribute("spellcheck", "false")
    if width then i.size = width end
    i:addEventListener("input", function()
        replace_symbols(i)
        if oninput then oninput() end
    end)
    return i
end
local function dirty(st)
    return function()
        if st then st.textContent = "" ; st.className = "st" end
        summary_el.textContent = ""
    end
end

local function split_hole(html)
    -- returns {pre, post} splitting at the first □ (3-byte UTF-8)
    local p = html:find("□", 1, true)
    if not p then return nil end
    return { html:sub(1, p-1), html:sub(p + #"□") }
end

-- ---------- skeleton rendering ----------
local function render_section(view, sec, si)
    local box = el("div", "sec")
    box:appendChild(text("div", sec.label, "seclabel"))
    if sec.bind and sec.bind ~= "" then
        box:appendChild(text("div", "where "..sec.bind, "bind"))
    end
    state.holes[si] = {}
    state.st[si] = {}
    for ri,row in ipairs(sec.rows) do
        local r = el("div", "row")
        local term = el("span", "term")
        local st = el("span", "st")
        if row.fixed then
            term.innerHTML = row.fixed
        else
            local frags = row.tmpl_html and split_hole(row.tmpl_html)
            if frags then
                local pre = el("span"); pre.innerHTML = frags[1]
                local post = el("span"); post.innerHTML = frags[2]
                local inp = mk_input("hole", 9, dirty(st))
                term:appendChild(pre); term:appendChild(inp); term:appendChild(post)
                state.holes[si][ri] = inp
            elseif row.tmpl_html then
                term.innerHTML = row.tmpl_html
            end
        end
        r:appendChild(term)
        r:appendChild(text("span", row.cite and ("— "..row.cite) or "", "cite"))
        r:appendChild(st)
        state.st[si][ri] = st
        box:appendChild(r)
    end
    return box
end

-- ---------- free-mode rendering ----------
local function add_free_row(block, si)
    local r = el("div", "row")
    local term = el("span", "term")
    local st = el("span", "st")
    local expr = mk_input("expr", 22, dirty(st))
    term:appendChild(expr)
    r:appendChild(term)
    local cite = el("span", "cite")
    local sel = el("select")
    local o0 = document:createElement("option")
    o0.value = ""; o0.textContent = "(rule)"
    sel:appendChild(o0)
    for _,c in ipairs(state.view.cites or {}) do
        local o = document:createElement("option")
        o.value = c; o.textContent = c
        sel:appendChild(o)
    end
    sel:addEventListener("change", dirty(st))
    cite:appendChild(sel)
    r:appendChild(cite)
    r:appendChild(st)
    local del = text("button", "×")
    del.style.padding = "2px 8px"
    local rowobj = { expr = expr, cite = sel, st = st, row_el = r }
    del:addEventListener("click", function()
        block.el:removeChild(r)
        for i,rr in ipairs(block.rows) do
            if rr == rowobj then table.remove(block.rows, i) break end
        end
        dirty(nil)()
    end)
    r:appendChild(del)
    block.el:appendChild(r)
    block.rows[#block.rows+1] = rowobj
end

local function render_free_block(secdef, si)
    local box = el("div", "sec")
    local label = secdef.label
    if secdef.optional then label = label .. "  (optional)" end
    box:appendChild(text("div", label, "seclabel"))
    local bindrow = el("div", "bind")
    bindrow:appendChild(text("span", "premise (optional): "))
    local bind_st = el("span", "st")
    local bind = mk_input(nil, 18, dirty(bind_st))
    bind.placeholder = "e.g. w = u·a"
    bindrow:appendChild(bind)
    bindrow:appendChild(bind_st)
    box:appendChild(bindrow)
    local block = { el = box, rows = {}, bind = bind, bind_st = bind_st }
    state.free_blocks[si] = block
    local add = text("button", "+ row")
    add.style.padding = "4px 12px"
    add:addEventListener("click", function()
        add_free_row(block, si); dirty(nil)() end)
    -- rows go above the add button: keep a container
    local rows_el = el("div")
    box:appendChild(rows_el)
    block.el = rows_el          -- rows appended into rows_el
    box:appendChild(add)
    add_free_row(block, si)
    add_free_row(block, si)
    return box
end

-- ---------- render dispatch ----------
local function render(view)
    state.view = view
    state.holes, state.st, state.free_blocks = {}, {}, {}
    state.ih_input, state.ih_st = nil, nil
    clear(proof_el); clear(summary_el)
    clear(ihrow_el); clear(rulesbox_el)
    goal_el.innerHTML = ""
    goal_el:appendChild(text("span", (view.title or "").."  ", "goaltitle"))
    if view.goal_html then
        local g = el("span", "goaleq")
        g.innerHTML = view.goal_html
        goal_el:appendChild(g)
    end
    if view.hint then
        goal_el:appendChild(text("div", view.hint, "hint"))
    end
    -- citable rules, verbatim (so "Thm 2.1.6" is inspectable on-page)
    if view.cite_docs and #view.cite_docs > 0 then
        rulesbox_el:appendChild(text("div", "You may cite:", "seclabel"))
        for _,d in ipairs(view.cite_docs) do
            local row = el("div", "rule")
            row:appendChild(text("span", d.label, "rulelabel"))
            row:appendChild(text("span", d.doc or "", "ruledoc"))
            rulesbox_el:appendChild(row)
        end
    end
    if view.free then
        ihrow_el:appendChild(text("span",
            "Induction hypothesis (IH):  ", "seclabel"))
        local ih_st = el("span", "st")
        local ih = mk_input(nil, 30, dirty(ih_st))
        ih.placeholder = "e.g. P(k) = Q(k)"
        state.ih_input, state.ih_st = ih, ih_st
        ihrow_el:appendChild(ih)
        ihrow_el:appendChild(ih_st)
        for si,secdef in ipairs(view.sec_labels or {}) do
            proof_el:appendChild(render_free_block(secdef, si))
        end
    else
        if view.ih then
            ihrow_el:appendChild(text("span",
                "Induction hypothesis (IH): ", "seclabel"))
            ihrow_el:appendChild(text("code", view.ih))
        end
        for si,sec in ipairs(view.sections) do
            proof_el:appendChild(render_section(view, sec, si))
        end
    end
end

-- ---------- request view/check ----------
local function request_view(id)
    state.id = id
    util.js_post_message(json.encode({ what="view", id=id }))
end

local function send_check()
    local view = state.view
    if not view then return end
    local data = { what="check", id=state.id, sections={} }
    if view.free then
        data.ih = state.ih_input and state.ih_input.value or ""
        for si,blk in pairs(state.free_blocks) do
            local rows, any = {}, false
            for ri,r in ipairs(blk.rows) do
                rows[ri] = { expr = r.expr.value, cite = r.cite.value }
                if r.expr.value:match("%S") then any = true end
            end
            -- skip sections left completely blank (e.g. optional parts)
            if any or (blk.bind.value or ""):match("%S") then
                data.sections[#data.sections+1] =
                    { si=si, bind_str=blk.bind.value, rows=rows }
            end
        end
    else
        for si,sec in ipairs(view.sections) do
            local rows = {}
            for ri,_ in ipairs(sec.rows) do
                local inp = state.holes[si] and state.holes[si][ri]
                rows[ri] = inp and { hole = inp.value } or {}
            end
            data.sections[#data.sections+1] = { si=si, rows=rows }
        end
    end
    util.js_post_message(json.encode(data))
end

-- ---------- paint results ----------
local KIND = {
    ok             = { "ok",     "✓" },
    noop           = { "fail",   "✗" },
    instance_fail  = { "fail",   "✗" },
    mismatch       = { "fail",   "✗" },
    endpoint       = { "fail",   "✗" },
    ih_unnecessary = { "warn",   "⚠" },
    pending        = { "pending","…" },
    missing_ih     = { "fail",   "✗" },
    parse          = { "fail",   "✗" },
    empty          = { "pending","□" },
}

local function paint_st(st, kind, extra)
    local k = KIND[kind] or KIND.pending
    st.className = "st " .. k[1]
    local s = k[2]
    if extra then s = s .. "  " .. extra end
    st.textContent = s
end

local function row_st_el(si, ri)
    if state.view and state.view.free then
        local blk = state.free_blocks[si]
        return blk and blk.rows[ri] and blk.rows[ri].st
    end
    return state.st[si] and state.st[si][ri]
end

local function clear_all_st()
    for _,sec in pairs(state.st) do
        for _,st in pairs(sec) do st.textContent=""; st.className="st" end
    end
    for _,blk in pairs(state.free_blocks) do
        blk.bind_st.textContent=""; blk.bind_st.className="st"
        for _,r in ipairs(blk.rows) do
            r.st.textContent=""; r.st.className="st"
        end
    end
    if state.ih_st then state.ih_st.textContent=""; state.ih_st.className="st" end
end

local function paint(res)
    clear_all_st()
    -- links first, then row statuses (a parse error should override the
    -- "…" a pending link would leave on the same cell)
    for _,sres in ipairs(res.sections or {}) do
        local si = sres.si
        if sres.msg then
            local blk = state.free_blocks[si]
            local st = (blk and blk.bind_st) or row_st_el(si, 1)
            if st then st.className="st fail"; st.textContent="✗ "..sres.msg end
        end
        for j,link in pairs(sres.links or {}) do
            local st = row_st_el(si, j+1)
            if st then
                local extra
                if link.cex then
                    if link.cex.err then
                        extra = "(" .. (link.cex.env or "?") .. "): "
                            .. link.cex.err
                    else
                        extra = (link.cex.env or "?") .. ":  "
                            .. (link.cex.lv or "?") .. " ≠ "
                            .. (link.cex.rv or "?")
                    end
                elseif link.msg and link.kind ~= "ok" then
                    extra = link.msg
                end
                paint_st(st, link.kind, extra)
            end
        end
        for ri,row in pairs(sres.rows or {}) do
            local st = row_st_el(si, ri)
            if st and row.kind and row.kind ~= "ok" then
                paint_st(st, row.kind, row.msg)
            end
        end
    end
    if state.ih_st and res.ih then
        local map = { ok={"ok","✓"}, parse={"fail","✗ IH syntax"},
                      instance_fail={"fail","✗ IH is not an identity"},
                      circular={"fail","✗ circular IH"} }
        local m = map[res.ih.kind] or {"fail","✗"}
        state.ih_st.className = "st " .. m[1]
        local extra = res.ih.msg and ("  "..res.ih.msg) or ""
        if res.ih.kind=="ok" and res.ih.step_var
           and res.ih.step_var ~= (state.view.step_var or "") then
            extra = "  (step variable: "..res.ih.step_var..")"
        end
        state.ih_st.textContent = m[2] .. extra
    end
    clear(summary_el)
    if res.ok then
        summary_el:appendChild(text("span", "proof verified ✓", "st ok"))
    else
        summary_el:appendChild(text("span",
            res.msg or "not yet fully verified.", "st fail"))
    end
end

-- ---------- tab bar ----------
local function current_task_id()
    local g = state.sheets
        and state.sheets[1] and state.sheets[1].groups[state.group_i]
    local sub = g and g.subtasks[state.sub_i]
    if not sub then return nil end
    if state.free and sub.free_id then return sub.free_id end
    return sub.id
end

local function select_task()
    local id = current_task_id()
    if id then request_view(id) end
end

local function render_tabs()
    clear(tabs_el); clear(subtabs_el)
    local sh = state.sheets and state.sheets[1]
    if not sh then return end
    for gi,g in ipairs(sh.groups) do
        local t = text("button", g.title,
            gi==state.group_i and "tab active" or "tab")
        t:addEventListener("click", function()
            state.group_i, state.sub_i = gi, 1
            render_tabs(); select_task()
        end)
        tabs_el:appendChild(t)
    end
    local g = sh.groups[state.group_i]
    for si,sub in ipairs(g.subtasks) do
        local label = sub.sub .. ")  " .. (sub.title or "")
        local t = el("button", si==state.sub_i and "subtab active" or "subtab")
        if sub.goal_html then t.innerHTML = sub.sub .. ")  " .. sub.goal_html
        else t.textContent = label end
        t:addEventListener("click", function()
            state.sub_i = si
            render_tabs(); select_task()
        end)
        subtabs_el:appendChild(t)
    end
    -- variant toggle: guided vs free (per subtask, student chooses)
    clear(variant_el)
    local sub = g.subtasks[state.sub_i]
    if sub and sub.free_id then
        variant_el:appendChild(text("span", "variant: ", "varlabel"))
        for _,v in ipairs{{free=false,label="guided"},{free=true,label="free proof"}} do
            local b = text("button", v.label,
                state.free==v.free and "vartab active" or "vartab")
            b:addEventListener("click", function()
                if state.free ~= v.free then
                    state.free = v.free
                    render_tabs(); select_task()
                end
            end)
            variant_el:appendChild(b)
        end
    end
end

-- ---------- events ----------
checkbtn:addEventListener("click", send_check)
-- NB: no js_post_message here — it is only wired after this module's
-- require() returns.  The worker pushes the task list itself on load.

-- ---------- message handler (worker -> gui) ----------
return function(data)
    local ok,msg = pcall(json.decode, data)
    if not ok then return end
    data = msg
    if data.what == "tasks" then
        state.sheets = data.sheets
        render_tabs()
        select_task()
    elseif data.what == "view" then
        if data.id == state.id then render(data.view) end
    elseif data.what == "result" then
        if data.id == state.id then paint(data.res) end
    end
end
