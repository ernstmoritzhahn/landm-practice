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
local savefile_btn, loadfile_btn = get("savefile"), get("loadfile")
local loadinput, stateta = get("loadinput"), get("stateta")
local loadtext_btn = get("loadtext")
local savedetails_el, savemsg_el = get("savedetails"), get("savemsg")
local syntaxhint_el = get("syntaxhint")

local PROOF_SYNTAX_HINT =
    'input: <code>\\lambda</code> → λ ·\n' ..
    '    concatenation = space or <code>·</code> ·\n' ..
    '    <code>w^R</code>, <code>w^(k+1)</code>, <code>w^k</code> ·\n' ..
    '    sum: <code>sum(i,0,n;k^i)</code> · <code>f(n)</code>'
local REGEXP_SYNTAX_HINT =
    'input: <code>\\lambda</code> → λ · union = <code>∪</code>' ..
    ' or <code>|</code> or <code>U</code> ·\n' ..
    '    concatenation = juxtaposition ·\n' ..
    '    postfixes: <code>*</code> <code>+</code> <code>^n</code> ·\n' ..
    '    <code>∅</code> = empty language · braces <code>{ }</code>' ..
    ' group too'

local state = {
    sheets = nil,          -- tab structure from the worker
    group_i = 1,           -- selected exercise-group tab
    sub_i   = 1,           -- selected subtask tab
    free    = false,       -- variant toggle
    pinned  = false,       -- ?exercise=<id>: fixed single group, no tab bar
    id = nil, view = nil,
    holes = {}, st = {}, free_blocks = {},
}

-- ?exercise=<group-id> embeds one exercise per page (Canvas gets one
-- iframe per Aufgabe); absent -> fall back to a group tab bar.
local ex_param, sub_param
pcall(function()
    local q = window.location.search or ""
    ex_param = q:match("exercise=([%w_%.%-]+)")
    sub_param = q:match("sub=([%w_%.%-]+)")
end)

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
    ["\\cup"]      = "∪",
    ["\\cdot"]     = "·",
}
local REGEXP_REPLACE = {
    ["|"] = "∪",
}
local function replace_symbols(e, extra)
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
    if extra then
        for k,v in pairs(extra) do
            local count
            e.value, count = e.value:gsub(k, v)
            if count > 0 then
                sel = sel - #k + 1
                e.selectionStart = sel
                e.selectionEnd = sel
            end
        end
    end
end
-- oninput: clear the given status cell + the summary (stale verdicts
-- must not survive edits)
local function mk_input(cls, width, oninput, extra_repl)
    local i = el("input", cls)
    i.type = "text"
    i:setAttribute("spellcheck", "false")
    if width then i.size = width end
    i:addEventListener("input", function()
        replace_symbols(i, extra_repl)
        if oninput then oninput() end
    end)
    return i
end
local save_local  -- forward declaration (persistence section below)

local function dirty(st)
    return function()
        if st then st.textContent = "" ; st.className = "st" end
        summary_el.textContent = ""
        if save_local then save_local() end
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

-- ---------- regexp task rendering (exercise 1.2) ----------
local function render_regexp_block(view)
    local box = el("div", "sec")
    box:appendChild(text("div",
        "Your regular expression E with L(E) = L:", "seclabel"))
    local r = el("div", "row")
    local st = el("span", "st")
    local inp = mk_input("expr", 42, dirty(st), REGEXP_REPLACE)
    inp.placeholder = "e.g. (a∪b)*ab(a∪b)*"
    r:appendChild(inp)
    r:appendChild(st)
    box:appendChild(r)
    state.regexp_input, state.regexp_st = inp, st
    return box
end

-- ---------- persistence (localStorage, keys "landm:<sheet>:<task>") ----------
local STORE_PREFIX = "landm:"
local function storage_key()
    local sh = state.sheets and state.sheets[1]
    return STORE_PREFIX .. (sh and sh.id or "sheet") .. ":" .. tostring(state.id)
end
local function ls_set(k, v)
    pcall(function() window.localStorage:setItem(k, v) end)
end
local function ls_get(k)
    local ok, v = pcall(function() return window.localStorage:getItem(k) end)
    return ok and v or nil
end

save_local = function()
    if not (state.id and state.view) then return end
    local rec = { free = state.view.free and true or false }
    if state.view.type == "regexp" then
        rec.expr = state.regexp_input and state.regexp_input.value or ""
        ls_set(storage_key(), json.encode(rec))
        return
    end
    if state.view.free then
        rec.ih = state.ih_input and state.ih_input.value or ""
        rec.secs = {}
        for si,blk in pairs(state.free_blocks) do
            local rows = {}
            for ri,r in ipairs(blk.rows) do
                rows[ri] = { e = r.expr.value, c = r.cite.value }
            end
            rec.secs[#rec.secs+1] = { si=si, bind=blk.bind.value, rows=rows }
        end
    else
        rec.holes = {}
        for si,rows in pairs(state.holes) do
            for ri,inp in pairs(rows) do
                if (inp.value or "") ~= "" then
                    rec.holes[si..":"..ri] = inp.value
                end
            end
        end
    end
    ls_set(storage_key(), json.encode(rec))
end

local function restore_local()
    local raw = ls_get(storage_key())
    if not raw then return end
    local ok, rec = pcall(json.decode, raw)
    if not (ok and type(rec) == "table") then return end
    if state.view.type == "regexp" then
        if state.regexp_input and type(rec.expr) == "string" then
            state.regexp_input.value = rec.expr
        end
        return
    end
    if state.view.free then
        if state.ih_input and type(rec.ih) == "string" then
            state.ih_input.value = rec.ih
        end
        for _,srec in ipairs(rec.secs or {}) do
            local blk = state.free_blocks[srec.si]
            if blk then
                blk.bind.value = srec.bind or ""
                local rows = srec.rows or {}
                while #blk.rows < #rows do add_free_row(blk, srec.si) end
                for ri,r in ipairs(rows) do
                    local row = blk.rows[ri]
                    if row then
                        row.expr.value = r.e or ""
                        row.cite.value = r.c or ""
                    end
                end
            end
        end
    else
        for k,v in pairs(rec.holes or {}) do
            local si,ri = k:match("^(%d+):(%d+)$")
            local inp = si and state.holes[tonumber(si)]
                        and state.holes[tonumber(si)][tonumber(ri)]
            if inp then inp.value = v end
        end
    end
end

local function dump_all()
    local ok, ls = pcall(function() return window.localStorage end)
    if not (ok and ls) then return nil end
    local data = {}
    pcall(function()
        for i = 0, (ls.length or 0) - 1 do
            local k = ls:key(i)
            if k and k:sub(1, #STORE_PREFIX) == STORE_PREFIX then
                data[k] = ls:getItem(k)
            end
        end
    end)
    return json.encode{ format="landm-practice-state", v=1,
        saved_at=os.date("!%Y-%m-%dT%H:%M:%SZ"), data=data }
end

local function import_all(text)
    local ok, env = pcall(json.decode, text)
    if not (ok and type(env) == "table"
            and env.format == "landm-practice-state"
            and type(env.data) == "table") then
        return nil, "not a saved-work file"
    end
    local n = 0
    for k,v in pairs(env.data) do
        if type(k) == "string" and k:sub(1, #STORE_PREFIX) == STORE_PREFIX
           and type(v) == "string" then
            ls_set(k, v); n = n + 1
        end
    end
    return n
end

local function save_note(s) savemsg_el.textContent = s end

-- ---------- render dispatch ----------
local function render(view)
    state.view = view
    state.holes, state.st, state.free_blocks = {}, {}, {}
    state.ih_input, state.ih_st = nil, nil
    state.regexp_input, state.regexp_st = nil, nil
    clear(proof_el); clear(summary_el)
    clear(ihrow_el); clear(rulesbox_el)
    goal_el.innerHTML = ""
    goal_el:appendChild(text("span", (view.title or "").."  ", "goaltitle"))
    if view.goal_html then
        local g = el("span", "goaleq")
        g.innerHTML = view.goal_html
        goal_el:appendChild(g)
    end
    if view.desc then
        goal_el:appendChild(text("div", view.desc, "desc"))
    end
    checkbtn.textContent = "Check proof"
    if syntaxhint_el then syntaxhint_el.innerHTML = PROOF_SYNTAX_HINT end
    if view.type == "regexp" then
        checkbtn.textContent = "Check"
        rulesbox_el.style.display = "none"
        if syntaxhint_el then
            syntaxhint_el.innerHTML = REGEXP_SYNTAX_HINT
        end
        proof_el:appendChild(render_regexp_block(view))
        restore_local()
        return
    end
    if view.hint then
        goal_el:appendChild(text("div", view.hint, "hint"))
    end
    -- citable rules, verbatim (so "Thm 2.1.6" is inspectable on-page)
    rulesbox_el.style.display =
        (view.cite_docs and #view.cite_docs > 0) and "" or "none"
    if view.cite_docs and #view.cite_docs > 0 then
        rulesbox_el:appendChild(text("div",
            state.free and "You may cite:" or "Rules used in this proof:",
            "seclabel"))
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
    restore_local()
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
    if view.type == "regexp" then
        data.expr = state.regexp_input and state.regexp_input.value or ""
        util.js_post_message(json.encode(data))
        return
    end
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
    too_large      = { "fail",   "✗" },
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
    if state.regexp_st then state.regexp_st.textContent=""; state.regexp_st.className="st" end
end

local function paint(res)
    clear_all_st()
    if state.view and state.view.type == "regexp" then
        if state.regexp_st then
            if res.ok then
                paint_st(state.regexp_st, "ok")
            else
                paint_st(state.regexp_st, res.kind or "mismatch", res.msg)
            end
        end
        clear(summary_el)
        if res.ok then
            summary_el:appendChild(text("span",
                "L(E) = L verified ✓", "st ok"))
        else
            summary_el:appendChild(text("span",
                res.msg or "not verified.", "st fail"))
        end
        return
    end
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
            if st and row.kind and row.kind ~= "ok"
                and row.msg ~= "(empty)" then
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
    if not state.pinned and #sh.groups > 1 then
    for gi,g in ipairs(sh.groups) do
        local t = text("button", g.title,
            gi==state.group_i and "tab active" or "tab")
        t:addEventListener("click", function()
            state.group_i, state.sub_i = gi, 1
            render_tabs(); select_task()
        end)
        tabs_el:appendChild(t)
    end
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

local function import_and_reload(text)
    local n, err = import_all(text)
    if n then
        save_note("restored "..n.." saved task(s) — all sheets")
        if state.id then request_view(state.id) end
    else
        save_note("load failed: "..(err or "?"))
    end
end

savefile_btn:addEventListener("click", function()
    save_local()
    local dump = dump_all()
    if not dump then save_note("browser storage unavailable") return end
    stateta.value = dump
    util.js_get("landm.download")("landm-saved-work.json", dump)
    save_note("file downloaded — it contains every exercise on every sheet")
end)
loadfile_btn:addEventListener("click", function() loadinput:click() end)
loadinput:addEventListener("change", function()
    util.js_get("landm.read_file")(loadinput, import_and_reload)
    loadinput.value = ""
end)
loadtext_btn:addEventListener("click", function() import_and_reload(stateta.value) end)
savedetails_el:addEventListener("toggle", function()
    if savedetails_el.open then stateta.value = dump_all() or "" end
end)
-- NB: no js_post_message here — it is only wired after this module's
-- require() returns.  The worker pushes the task list itself on load.

-- ---------- message handler (worker -> gui) ----------
return function(data)
    local ok,msg = pcall(json.decode, data)
    if not ok then return end
    data = msg
    if data.what == "tasks" then
        state.sheets = data.sheets
        if ex_param then
            for gi,g in ipairs(state.sheets[1].groups) do
                if g.id == ex_param then
                    state.group_i, state.pinned = gi, true
                    break
                end
            end
        end
        if sub_param then
            local g = state.sheets[1].groups[state.group_i]
            for si,sub in ipairs(g.subtasks) do
                if sub.sub == sub_param then state.sub_i = si break end
            end
        end
        render_tabs()
        select_task()
    elseif data.what == "view" then
        if data.id == state.id then render(data.view) end
    elseif data.what == "result" then
        if data.id == state.id then paint(data.res) end
    end
end
