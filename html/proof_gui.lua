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
local PARTS_SYNTAX_HINT =
    'runs: state sequence, e.g. <code>q0 q0 q1 q2</code>' ..
    ' (start state optional) ·\n' ..
    '    regex: <code>∪</code>/<code>|</code> union · juxtaposition' ..
    ' concat · <code>*</code> <code>+</code> ·' ..
    ' <code>\\lambda</code> → λ · <code>∅</code> = empty language'

local state = {
    sheets = nil,          -- tab structure from the worker
    sheet_i = 1,           -- selected sheet (only ?exercise= switches)
    group_i = 1,           -- selected exercise-group tab
    sub_i   = 1,           -- selected subtask tab
    free    = false,       -- variant toggle
    pinned  = false,       -- ?exercise=<id>: fixed single group, no tab bar
    id = nil, view = nil,
    holes = {}, st = {}, free_blocks = {},
    parts = {},
}

-- the current sheet; everywhere the UI said sheets[1] it now means
-- the sheet that holds the selected group
local function cur_sheet()
    return state.sheets and state.sheets[state.sheet_i]
end

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
-- typed arrows become real arrows while typing, like the exam's
-- input helper:  => and -> both mean ⇒ in a derivation, → in a rule
local DERIV_REPLACE = {
    ["=>"] = "⇒", ["%->"] = "⇒", ["lambda"] = "λ",
}
local GRAMMAR_REPLACE = {
    ["%->"] = "→", ["=>"] = "→", ["lambda"] = "λ",
}
local TREE_REPLACE = {
    ["lambda"] = "λ",
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

-- ---------- composite "parts" tasks (exercise 1.3) ----------
-- kinds: aut (automata-app editor), table (transition table),
-- trace (run state sequences), accept (per-word yes/no),
-- regexp (regular expression field)
local function landm_call(name, ...)
    -- lua-interop: the FIRST Lua argument arrives JS-side as `this`,
    -- not positionally — prepend a throwaway so real args line up
    return util.js_get("landm." .. name)(false, ...)
end

local aut_id_seq = 0
local pending_aut = {}      -- editor boots only once the host is in the DOM
local send_check            -- forward decl: per-part buttons call it
local paint_st              -- forward decl: send_check marks pending

local function mount_aut(host, cfg_tbl, readonly, pi)
    -- ids, not element handles, cross the Lua<->JS bridge
    aut_id_seq = aut_id_seq + 1
    local host_id = "authost-" .. aut_id_seq
    local app_id  = "autapp-" .. aut_id_seq
    host.id = host_id
    pending_aut[#pending_aut + 1] =
        { host_id = host_id, app_id = app_id, pi = pi,
          cfg = json.encode(cfg_tbl), readonly = readonly }
    return app_id
end

local function boot_pending_aut()
    for _,p in ipairs(pending_aut) do
        landm_call("aut_boot", p.host_id, p.app_id, p.cfg)
        if p.readonly then
            landm_call("aut_readonly", p.app_id, true)
        else
            local pi = p.pi
            landm_call("aut_on_edit", p.app_id, function()
                dirty(nil)()
                if pi then refresh_dependents_of(pi) end
            end)
        end
    end
    pending_aut = {}
end

local function aut_cfg(v)
    return { mode="aut",
             aut_type = v.aut_type or "dfa",
             alphabet = v.alphabet or "",
             stack_alphabet = v.stack_alphabet or "",
             checks   = v.checks,
             initial  = v.initial or v.model }
end

local function acc_mark(pv, q)
    local m = q
    if pv.initial == q then m = "→ " .. m end
    for _,a in ipairs(pv.accepting or {}) do
        if a == q then m = m .. "  ★" end
    end
    return m
end

-- model -> graphviz dot for the compact static rendering of a given
-- machine (keeps the student's mental picture of the sheet's diagram:
-- same state names, same labels; layout is graphviz's own)
local function model_dot(model)
    -- tolerate shorthand models: states may be name strings and
    -- transitions may reference them by name via from/target
    local by_id, seq = {}, {}
    for i, s in ipairs(model.states or {}) do
        if type(s) ~= "table" then s = { id = i, name = s } end
        by_id[s.id] = s
        if s.name then by_id[s.name] = s end
        seq[#seq + 1] = s
    end
    local d = { 'digraph G { rankdir=LR; bgcolor="transparent";'
        .. ' node [shape=circle, width=0.45, fixedsize=true,'
        .. ' fontsize=12]; edge [fontsize=11, arrowsize=0.7];' }
    d[#d + 1] = '__start [shape=point, width=0.02, label=""];'
    local edges = {}
    for _, s in ipairs(seq) do
        d[#d + 1] = '"' .. tostring(s.name) .. '" ['
            .. (s.accepting and 'shape=doublecircle,' or '') .. '];'
        if s.initial then
            d[#d + 1] = '__start -> "' .. tostring(s.name) .. '";'
        end
    end
    local seen = {}
    for _, t in ipairs(model.transitions or {}) do
        local f = by_id[t.from] and by_id[t.from].name
        local tt = by_id[t.to or t.target]
                  and by_id[t.to or t.target].name
        if f and tt then
            local key = f .. "\1" .. tt
            local lab = (t.label == "" or t.label == "λ")
                and "λ" or t.label
            edges[key] = edges[key] and (edges[key] .. "," .. lab)
                or lab
            seen[key] = { f, tt }
        end
    end
    for k, e in pairs(seen) do
        d[#d + 1] = '"' .. e[1] .. '" -> "' .. e[2]
            .. '" [label="' .. edges[k] .. '"];'
    end
    d[#d + 1] = "}"
    return table.concat(d, "\n")
end

local function mount_given_svg(host, model, label)
    if label then
        host:appendChild(text("span", label, "glabel"))
    end
    local svgdiv = el("div", "givensvg")
    host:appendChild(svgdiv)
    landm_call("graphviz", model_dot(model), function(svg)
        if svg and svg ~= "" then svgdiv.innerHTML = svg end
    end)
end

local function render_given(g)
    local box = el("div", "givenbox")
    if g[1] then
        for _, item in ipairs(g) do
            box:appendChild(render_given(item))
        end
        return box
    end
    if g.kind == "text" then
        local pre = el("pre", "giventext")
        pre.textContent = g.text
        box:appendChild(pre)
    elseif g.kind == "table" then
        local tb = el("table", "trtable")
        local hr = el("tr")
        hr:appendChild(text("th", "δ"))
        for _,s in ipairs(g.symbols) do hr:appendChild(text("th", s)) end
        tb:appendChild(hr)
        for _,row in ipairs(g.rows) do
            local tr = el("tr")
            local mark = (row.initial and "→ " or "") .. row.state
                .. (row.accepting and "  ★" or "")
            tr:appendChild(text("td", mark))
            for _,s in ipairs(g.symbols) do
                tr:appendChild(text("td", tostring(row[s] or "—")))
            end
            tb:appendChild(tr)
        end
        box:appendChild(tb)
    elseif g.kind == "aut" then
        mount_given_svg(box, g.model, g.label)
    end
    return box
end

-- merge the model of part `spi`'s editor into `rec`'s editor: states
-- are copied with fresh ids, prefixed names ("a_q0") and an offset so
-- the construction step can wire them further.  The first inserted
-- seed keeps its initial flag; later seeds arrive un-initial so the
-- "one initial state" rule picks the global start deliberately.
local function insert_seed(rec, spi)
    local seed = state.parts[spi]
    if not (seed and seed.app and rec.app) then return end
    local ok_s, sm = pcall(json.decode,
        landm_call("aut_state", seed.app) or "")
    local ok_c, cm = pcall(json.decode,
        landm_call("aut_state", rec.app) or "")
    if not (ok_s and type(sm) == "table" and sm.states) then return end
    -- retrieveData() is "" for an untouched editor — an empty model
    -- is a fine merge target, synthesise the skeleton
    if not (ok_c and type(cm) == "table" and cm.states) then
        cm = { type = rec.aut_type or sm.type or "nfa-eps",
               alphabet = sm.alphabet,
               states = {}, transitions = {} }
    end
    local max_id, max_x, has_init = 0, nil, false
    for _, s in ipairs(cm.states) do
        if (s.id or 0) > max_id then max_id = s.id end
        if not max_x or (s.x or 0) > max_x then max_x = s.x end
        if s.initial then has_init = true end
    end
    for _, t in ipairs(cm.transitions or {}) do
        if (t.id or 0) > max_id then max_id = t.id end
    end
    local smin_x, smin_y
    for _, s in ipairs(sm.states) do
        smin_x = math.min(smin_x or s.x or 0, s.x or 0)
        smin_y = math.min(smin_y or s.y or 0, s.y or 0)
    end
    if not smin_x then return end   -- seed editor is empty
    local dx = (max_x or -66) + 132 - smin_x
    local dy = 66 - smin_y
    local idmap = {}
    local pre = string.char(96 + spi) .. "_"
    for _, s in ipairs(sm.states) do
        max_id = max_id + 1
        idmap[s.id] = max_id
        local keep_init = s.initial and not has_init
        if keep_init then has_init = true end
        cm.states[#cm.states + 1] = {
            id = max_id,
            name = pre .. tostring(s.name or s.id),
            x = (s.x or 0) + dx, y = (s.y or 0) + dy,
            initial = keep_init and true or false,
            accepting = s.accepting and true or false }
    end
    cm.transitions = cm.transitions or {}
    for _, t in ipairs(sm.transitions or {}) do
        if idmap[t.from] and idmap[t.to] then
            max_id = max_id + 1
            cm.transitions[#cm.transitions + 1] = {
                id = max_id, from = idmap[t.from], to = idmap[t.to],
                label = t.label }
        end
    end
    landm_call("aut_load", rec.app, json.encode(cm))
end

-- ---------- guided construction: locked components + simplify ----------
-- a stage's effective automaton: its simplify output when that has
-- content, else the compose editor's content.  Returns a decoded model
-- table or nil for an empty stage.
local function stage_aut_json(sid)
    local e = state.stage_map and state.stage_map[sid]
    if not e then return nil end
    local function app_model(pi)
        local p = state.parts[pi]
        if not (p and p.app) then return nil end
        local s = landm_call("aut_state", p.app)
        if not s or s == "" then return nil end
        local ok, m = pcall(json.decode, s)
        if not (ok and type(m) == "table"
                and m.states and #m.states > 0) then
            return nil
        end
        return m
    end
    if e.simplify then
        local m = app_model(e.simplify)
        if m then return m end
    end
    return app_model(e.compose)
end

local GGRID = 66

-- embed the stage's effective automaton as a locked, tagged component.
-- Name-preserving merge: embedded nodes that still appear in the stage
-- automaton keep position AND wiring flags (a refresh after the student
-- already wired flags does not undo that work); stale tagged nodes are
-- removed — student edges incident to them are retargeted by role
-- (the old entry's successors attach to the new entry, likewise the
-- old exit).  The same retargeting applies when a kept node LOSES its
-- entry/exit role to a different state (e.g. a newly added state takes
-- over as final): connections to the special states stay, re-pointed
-- at their successors; missing nodes are placed right of the kept
-- block (or of all content on first embed).  The stage's internal
-- transitions are rebuilt to match — other student edges are
-- untouched.
local function upsert_component(m, tag, sm)
    -- tag names the embedded copy ("b", "b#2"); # is not name-safe so
    -- node names use the #-stripped prefix while .seed keeps the tag
    local prefix = tag:gsub("#", "_") .. "_"
    m.states = m.states or {}
    m.transitions = m.transitions or {}
    local want_names = {}
    for _, s in ipairs(sm.states or {}) do
        want_names[prefix .. tostring(s.name or s.id)] = true
    end
    -- 1. drop stale embedded nodes (+ incident edges); student edges
    -- that ran to a stale node are kept aside for retargeting — the
    -- role it played (entry/exit) names its successor under the new
    -- component version
    local dead = {}
    local dropped = {}
    local kept_states = {}
    for _, s in ipairs(m.states) do
        if s.seed == tag
           and not want_names[tostring(s.name or s.id)] then
            dead[s.id] = { entry = s.seed_entry and true or false,
                           exit = s.seed_exit and true or false }
        else
            kept_states[#kept_states + 1] = s
        end
    end
    m.states = kept_states
    if next(dead) then
        local kept_tr = {}
        for _, e in ipairs(m.transitions) do
            if dead[e.from] or dead[e.to] then
                if e.seed ~= tag then
                    dropped[#dropped + 1] = e
                end
            else
                kept_tr[#kept_tr + 1] = e
            end
        end
        m.transitions = kept_tr
    end
    -- 2. indexes: by name, by seed-node id; keep-matched nodes stay put
    local by_name, next_id = {}, 0
    for _, s in ipairs(m.states) do
        by_name[tostring(s.name or s.id)] = s
        if type(s.id) == "number" and s.id > next_id then
            next_id = s.id
        end
    end
    for _, e in ipairs(m.transitions) do
        if type(e.id) == "number" and e.id > next_id then
            next_id = e.id
        end
    end
    local name_of = {}              -- seed node id -> result node
    local demoted = {}              -- kept node id -> roles it lost
    for _, s in ipairs(sm.states or {}) do
        local wn = prefix .. tostring(s.name or s.id)
        local n = by_name[wn]
        -- a node carrying the component's reserved name IS that
        -- component state — regardless of a lost seed tag (hand-edited
        -- JSON, stale bundle); claim it instead of duplicating
        if n then
            -- record the roles this node held BEFORE the refresh:
            -- a kept node that loses entry/exit to a new state gets
            -- its student edges retargeted just like a deleted one
            local was_entry = n.seed_entry and true or false
            local was_exit = n.seed_exit and true or false
            n.locked = true
            n.seed = tag
            -- the component's own entry/exit markers follow the
            -- stage automaton's flags on every refresh
            n.seed_entry = s.initial and true or nil
            n.seed_exit = s.accepting and true or nil
            local l_entry = was_entry and not n.seed_entry
            local l_exit = was_exit and not n.seed_exit
            if l_entry or l_exit then
                demoted[n.id] = { entry = l_entry, exit = l_exit }
            end
            name_of[tostring(s.id)] = n     -- keep position + flags
        end
    end
    -- anchor for fresh nodes: keep the block's current min corner when
    -- anything survived, else append right of the content bbox
    local mnx, mny
    for _, s in ipairs(sm.states or {}) do
        local x, y = s.x or 0, s.y or 0
        if not mnx or x < mnx then mnx = x end
        if not mny or y < mny then mny = y end
    end
    if not mnx then return end   -- empty stage automaton
    local bx, by
    if next(name_of) then
        for _, n in pairs(name_of) do
            if not bx or n.x < bx then bx = n.x end
            if not by or n.y < by then by = n.y end
        end
        bx, by = bx - mnx, by - mny
    else
        local maxx = nil
        for _, s in ipairs(m.states) do
            if type(s.x) == "number"
               and (not maxx or s.x > maxx) then maxx = s.x end
        end
        bx = (maxx and (maxx + 3 * GGRID) or GGRID) - mnx
        by = GGRID - mny
    end
    -- 3. add missing nodes (flags stripped: initial/accepting on a
    -- component state is a wiring choice the student makes)
    for _, s in ipairs(sm.states or {}) do
        if not name_of[tostring(s.id)] then
            next_id = next_id + 1
            local n = { id = next_id,
                        name = prefix .. tostring(s.name or s.id),
                        x = (s.x or 0) + bx, y = (s.y or 0) + by,
                        initial = false, accepting = false,
                        locked = true, seed = tag,
                        seed_entry = s.initial and true or nil,
                        seed_exit = s.accepting and true or nil }
            m.states[#m.states + 1] = n
            name_of[tostring(s.id)] = n
            by_name[n.name] = n
        end
    end
    -- 3b. retarget student edges that touched a boundary state whose
    -- role moved on: either the node was dropped in step 1, or it
    -- survived but is no longer the component's entry/exit.  An edge
    -- that left such a node reconnects from the NEW exit state, one
    -- that entered it reconnects to the NEW entry state (composable
    -- components have exactly one of each); edges touching a vanished
    -- interior state are dropped
    if #dropped > 0 or next(demoted) then
        local new_entry, new_exit
        for _, s in ipairs(sm.states or {}) do
            local n = name_of[tostring(s.id)]
            if s.initial then new_entry = n end
            if s.accepting then new_exit = n end
        end
        -- kept nodes that lost their role: rewrite live edges in place
        local live = {}
        for _, e in ipairs(m.transitions) do
            if e.seed ~= tag then
                local fd, td = demoted[e.from], demoted[e.to]
                if fd then
                    local f = (fd.exit and new_exit)
                              or (fd.entry and new_entry)
                    if f then e.from = f.id else fd = "drop" end
                end
                if td then
                    local t = (td.entry and new_entry)
                              or (td.exit and new_exit)
                    if t then e.to = t.id else td = "drop" end
                end
                if fd ~= "drop" and td ~= "drop" then
                    live[#live + 1] = e
                end
            else
                live[#live + 1] = e
            end
        end
        m.transitions = live
        for _, e in ipairs(dropped) do
            local fd, td = dead[e.from], dead[e.to]
            local f = fd and ((fd.exit and new_exit)
                              or (fd.entry and new_entry)) or nil
            local t = td and ((td.entry and new_entry)
                              or (td.exit and new_exit)) or nil
            local fi = f and f.id or (not fd and e.from)
            local ti = t and t.id or (not td and e.to)
            if fi and ti then
                next_id = next_id + 1
                m.transitions[#m.transitions + 1] = {
                    id = next_id, from = fi, to = ti,
                    label = e.label or "" }
            end
        end
    end
    -- 4. rebuild the stage's internal edges verbatim
    local kept_tr = {}
    for _, e in ipairs(m.transitions) do
        if e.seed ~= tag then kept_tr[#kept_tr + 1] = e end
    end
    m.transitions = kept_tr
    for _, e in ipairs(sm.transitions or {}) do
        local f, t = name_of[tostring(e.from)], name_of[tostring(e.to)]
        if f and t then
            next_id = next_id + 1
            m.transitions[#m.transitions + 1] = {
                id = next_id, from = f.id, to = t.id,
                label = e.label or "", locked = true, seed = tag }
        end
    end
end

local function refresh_components(pi)
    local pv = state.view.parts[pi]
    local p = state.parts[pi]
    if not (pv and p and p.app) then return end
    local ok, m = pcall(json.decode,
        landm_call("aut_state", p.app) or "")
    if not (ok and type(m) == "table" and m.states) then
        m = { type = p.aut_type or "nfa-eps", alphabet = pv.alphabet,
              states = {}, transitions = {} }
    end
    for _, tag in ipairs(pv.seeds_locked or {}) do
        local stage = tag:match("^[^#]+") or tag
        local sm = stage_aut_json(stage)
        if sm then upsert_component(m, tag, sm) end
    end
    landm_call("aut_load", p.app, json.encode(m))
end

-- auto-sync: an edit in a part that DEFINES a stage (its compose
-- editor via pv.sid, its simplify slot via pv.takeover_from)
-- re-embeds that stage's effective automaton in every part that lists
-- it among seeds_locked.  aut_load is suppressed by the editor's dirty
-- counter, so refreshed canvases do NOT re-fire the edit hook — the
-- cascade down the stage chain is walked explicitly instead (parts
-- only embed earlier stages, so the walk terminates).
function refresh_dependents_of(pi)
    local parts = state.view and state.view.parts
    if not parts then return end
    local pv = parts[pi]
    if not pv then return end
    local queue, done = {}, {}
    if pv.sid then queue[#queue + 1] = pv.sid end
    if pv.takeover_from then queue[#queue + 1] = pv.takeover_from end
    while #queue > 0 do
        local sid = table.remove(queue, 1)
        for dpi, dpv in ipairs(parts) do
            if not done[dpi] and dpv.seeds_locked then
                local hit = false
                for _, tag in ipairs(dpv.seeds_locked) do
                    if (tag:match("^[^#]+") or tag) == sid then
                        hit = true break
                    end
                end
                if hit then
                    done[dpi] = true
                    refresh_components(dpi)
                    -- the refreshed part may itself define a stage —
                    -- its dependents follow
                    if dpv.sid then queue[#queue + 1] = dpv.sid end
                end
            end
        end
    end
end

-- simplify slot: take over the stage's compose automaton as a plain,
-- fully editable copy (locks/tags stripped — manual simplification
-- must be able to remove anything)
local function takeover_simplify(pi)
    local pv = state.view.parts[pi]
    local p = state.parts[pi]
    local e = pv and state.stage_map
              and state.stage_map[pv.takeover_from]
    local cp = e and state.parts[e.compose]
    if not (cp and cp.app and p and p.app) then return end
    local ok, m = pcall(json.decode,
        landm_call("aut_state", cp.app) or "")
    if not (ok and type(m) == "table" and m.states
            and #m.states > 0) then return end
    for _, s in ipairs(m.states) do
        s.locked, s.seed = nil, nil
        s.seed_entry, s.seed_exit = nil, nil
    end
    for _, t in ipairs(m.transitions or {}) do
        t.locked, t.seed = nil, nil
    end
    landm_call("aut_load", p.app, json.encode(m))
    dirty(nil)()
    -- aut_load is dirty-suppressed, so the new stage content would
    -- not propagate by itself — refresh dependent parts explicitly
    refresh_dependents_of(pi)
end

-- ---------- sheet-3 helpers: pumping splits, min_table ----------
local function pairkey(a, b)
    return (a < b) and (a .. "|" .. b) or (b .. "|" .. a)
end
local function pair_enum(states)
    local out = {}
    for i = 1, #states do
        for j = i + 1, #states do
            out[#out + 1] = { a = states[i], b = states[j],
                              key = pairkey(states[i], states[j]) }
        end
    end
    return out
end
local function clear_pump_rows(p)
    if p.splitbox then clear(p.splitbox) end
    p.i_inps, p.row_st = {}, {}
    p.gen, p.gen_st, p.last_k = nil, nil, nil
end
local function request_splits(pi)
    local p = state.parts[pi]
    if not (p and p.z) then return end
    util.js_post_message(json.encode(
        { what="pump_splits", id=state.id, pi=pi, z=p.z.value,
          k=p.ksel and tonumber(p.ksel.value) or nil }))
end
-- (re)build the distinguishing-word rows for the ticked pairs;
-- values survive via the `old` stash
local function rebuild_wit(pi)
    local p = state.parts[pi]
    if not (p and p.witbox) then return end
    local old = {}
    for k, inp in pairs(p.wit or {}) do old[k] = inp.value end
    clear(p.witbox)
    p.wit, p.row_st = {}, {}
    for idx, pr in ipairs(p.pairs) do
        local c = p.cells[pr.key]
        if c and c.cb and c.cb.checked then
            local r = el("div", "wordrow")
            r:appendChild(text("span",
                "w for {" .. pr.a .. "," .. pr.b .. "}:", "wlabel"))
            local rst = el("span", "st")
            local inp = mk_input(nil, 12, dirty(rst))
            inp.value = old[pr.key] or ""
            r:appendChild(inp); r:appendChild(rst)
            p.witbox:appendChild(r)
            p.wit[pr.key], p.row_st[idx] = inp, rst
        end
    end
end

local function render_part(pv, pi)
    local box = el("div", "part")
    local lab = el("div", "partlabel")
    lab:appendChild(text("span", pv.sub, "psub"))
    lab:appendChild(text("span", pv.label or ""))
    local st = el("span", "st")
    lab:appendChild(st)
    local chk = el("button", "pcheck")
    chk.textContent = "Check"
    chk:addEventListener("click", function() send_check(pi) end)
    lab:appendChild(chk)
    box:appendChild(lab)
    local rec = { kind = pv.kind, st = st }
    state.parts[pi] = rec
    if pv.kind == "aut" then
        local row = el("div", "autrow")
        box:appendChild(row)
        local host = el("div", "authost")
        row:appendChild(host)
        rec.app = mount_aut(host, aut_cfg(pv), false, pi)
        rec.aut_type = pv.aut_type
        -- mini views of the relevant given machines, next to the
        -- editor, plus an "insert" button that copies one in
        local gv = state.view and state.view.given
        local side
        local function sidehost()
            if not side then
                side = el("div", "autside")
                row:appendChild(side)
            end
            return side
        end
        for _, gi in ipairs(pv.show_given or {}) do
            local g = gv and gv[gi]
            if g and g.kind == "aut" and g.model then
                mount_given_svg(sidehost(), g.model,
                                g.label or "given")
            end
        end
        if pv.copy then
            local g = gv and gv[pv.copy]
            if g and g.kind == "aut" and g.model then
                mount_given_svg(sidehost(), g.model,
                                g.label or "given")
                local btn = el("button", "seedbtn")
                btn.textContent = "insert "
                    .. (g.label or "the given automaton")
                btn:addEventListener("click", function()
                    landm_call("aut_load", rec.app,
                               json.encode(g.model))
                    dirty(st)()
                end)
                sidehost():appendChild(btn)
            end
        end
        if pv.seeds and #pv.seeds > 0 then
            local sr = el("div", "wordrow")
            sr:appendChild(text("span",
                "insert automaton from part:", "wlabel"))
            local sel = el("select")
            for _, spi in ipairs(pv.seeds) do
                local op = document:createElement("option")
                op.value = tostring(spi)
                local spv = state.view and state.view.parts
                          and state.view.parts[spi]
                op.textContent = (spv and spv.sub)
                    or (string.char(96 + spi) .. ")")
                sel:appendChild(op)
            end
            local btn = el("button", "seedbtn")
            btn.textContent = "insert"
            btn:addEventListener("click", function()
                insert_seed(rec, tonumber(sel.value))
            end)
            sr:appendChild(sel); sr:appendChild(btn)
            box:appendChild(sr)
        end
        if pv.seeds_locked and #pv.seeds_locked > 0 then
            -- guided composition: the previous steps' automata are
            -- given as locked components; refresh re-syncs them with
            -- the (possibly simplified) current content of those steps
            local sr = el("div", "wordrow")
            local labels = {}
            for _, s in ipairs(pv.seeds_locked) do
                labels[#labels + 1] = s .. ")"
            end
            sr:appendChild(text("span",
                "given components: " .. table.concat(labels, ", ")
                .. "  (kept in sync automatically)",
                "wlabel"))
            local btn = el("button", "seedbtn")
            btn.textContent = "refresh now"
            btn:addEventListener("click", function()
                refresh_components(pi)
            end)
            sr:appendChild(btn)
            box:appendChild(sr)
        end
        if pv.takeover_from then
            local sr = el("div", "wordrow")
            sr:appendChild(text("span",
                "simplify (optional): take over, then reduce — "
                .. "if used, this becomes the next step's component",
                "wlabel"))
            local btn = el("button", "seedbtn")
            btn.textContent = "take over the automaton"
            btn:addEventListener("click", function()
                takeover_simplify(pi)
            end)
            sr:appendChild(btn)
            box:appendChild(sr)
        end
        if pv.with_regexp then
            local r = el("div", "wordrow")
            r:appendChild(text("span",
                "regular expression (optional):", "wlabel"))
            local rst = el("span", "st")
            local inp = mk_input("expr", 30, dirty(rst), REGEXP_REPLACE)
            r:appendChild(inp); r:appendChild(rst)
            box:appendChild(r)
            rec.re, rec.re_st = inp, rst
        end
    elseif pv.kind == "trace" then
        rec.seqs, rec.row_st = {}, {}
        for wi,w in ipairs(pv.words or {}) do
            local r = el("div", "wordrow")
            r:appendChild(text("span", "w = " .. w .. ":", "wlabel"))
            local rst = el("span", "st")
            local inp = mk_input("expr", 30, dirty(rst))
            inp.placeholder = "q0 q0 q1 q2 q2"
            r:appendChild(inp); r:appendChild(rst)
            box:appendChild(r)
            rec.seqs[wi], rec.row_st[wi] = inp, rst
        end
    elseif pv.kind == "accept" then
        rec.ans, rec.row_st = {}, {}
        for wi,w in ipairs(pv.words or {}) do
            local r = el("div", "wordrow")
            r:appendChild(text("span", "w = " .. w, "wlabel"))
            local sel = el("select")
            for _,o in ipairs{{"","(choose)"},
                              {"yes","accepted"},
                              {"no","not accepted"}} do
                local op = document:createElement("option")
                op.value, op.textContent = o[1], o[2]
                sel:appendChild(op)
            end
            local rst = el("span", "st")
            sel:addEventListener("change", dirty(rst))
            r:appendChild(sel); r:appendChild(rst)
            box:appendChild(r)
            rec.ans[wi], rec.row_st[wi] = sel, rst
        end
    elseif pv.kind == "table" or pv.kind == "stable" then
        local tb = el("table", "trtable")
        local hr = el("tr")
        hr:appendChild(text("th", pv.kind == "stable" and "t" or "δ"))
        for _,s in ipairs(pv.alphabet or {}) do
            hr:appendChild(text("th", s))
        end
        tb:appendChild(hr)
        rec.cells = {}
        for i,q in ipairs(pv.states or {}) do
            local tr = el("tr")
            tr:appendChild(text("td", acc_mark(pv, q)))
            for _,s in ipairs(pv.alphabet or {}) do
                local td = el("td")
                local inp = mk_input(nil, pv.kind == "stable" and 9 or 4,
                                     dirty(nil))
                td:appendChild(inp)
                tr:appendChild(td)
                rec.cells[i .. "|" .. s] = { input = inp, td = td }
            end
            tb:appendChild(tr)
        end
        box:appendChild(tb)
    elseif pv.kind == "closure" then
        rec.sets, rec.row_st = {}, {}
        for wi,q in ipairs(pv.states or {}) do
            local r = el("div", "wordrow")
            r:appendChild(text("span",
                "λ-closure(" .. q .. ") =", "wlabel"))
            local rst = el("span", "st")
            local inp = mk_input("expr", 20, dirty(rst))
            inp.placeholder = "{q0, q2}"
            r:appendChild(inp); r:appendChild(rst)
            box:appendChild(r)
            rec.sets[wi], rec.row_st[wi] = inp, rst
        end
    elseif pv.kind == "regexp" then
        local r = el("div", "wordrow")
        local rst = el("span", "st")
        local inp = mk_input("expr", 40, dirty(rst), REGEXP_REPLACE)
        inp.placeholder = "e.g. (a∪b)*ab(a∪b)*"
        r:appendChild(inp); r:appendChild(rst)
        box:appendChild(r)
        rec.expr, rec.expr_st = inp, rst
    elseif pv.kind == "choice" then
        rec.sels = {}
        rec.cells = {}
        for _, slot in ipairs(pv.slots or {}) do
            local r = el("div", "wordrow")
            r:appendChild(text("span", (slot.label or slot.key) .. ":", "wlabel"))
            local sel = document:createElement("select")
            local o0 = document:createElement("option")
            o0.value, o0.textContent = "", "(choose)"
            sel:appendChild(o0)
            for _, o in ipairs(slot.options or {}) do
                local op = document:createElement("option")
                op.value, op.textContent = o.id, o.label
                sel:appendChild(op)
            end
            local rst = el("span", "st")
            sel:addEventListener("change", dirty(rst))
            r:appendChild(sel); r:appendChild(rst)
            box:appendChild(r)
            rec.sels[slot.key] = sel
            rec.cells["sel_" .. slot.key] = { td = rst }
        end
    elseif pv.kind == "pumping" then
        local r = el("div", "wordrow")
        r:appendChild(text("span", "z(k) =", "wlabel"))
        local zst = el("span", "st")
        local zinp = mk_input("expr", 26, function()
            dirty(zst)()
            clear_pump_rows(rec)
        end)
        zinp.placeholder = "e.g. a^k b^k  (^k )^k"
        r:appendChild(zinp)
        local btn = document:createElement("button")
        btn.className, btn.textContent = "seedbtn", "decompose"
        btn:addEventListener("click", function() request_splits(pi) end)
        r:appendChild(btn)
        local ksel = document:createElement("select")
        for kv = 2, 5 do
            local o = document:createElement("option")
            o.value, o.textContent = tostring(kv), "k = " .. kv
            ksel:appendChild(o)
        end
        ksel.value = "3"
        ksel:addEventListener("change", function()
            dirty(zst)()
            request_splits(pi)
        end)
        r:appendChild(ksel); r:appendChild(zst)
        rec.ksel = ksel
        box:appendChild(r)
        local sp = el("div")
        box:appendChild(sp)
        rec.z, rec.z_st, rec.splitbox = zinp, zst, sp
        rec.i_inps, rec.row_st = {}, {}
        rec.cells = { z = { td = zst } }
    elseif pv.kind == "min_table" then
        local states = pv.states or {}
        rec.pairs = pair_enum(states)
        rec.cells, rec.row_st = {}, {}
        local tb = el("table", "trtable")
        local hr = el("tr")
        hr:appendChild(text("th", "D[i,j]"))
        for j = 2, #states do
            hr:appendChild(text("th", states[j]))
        end
        tb:appendChild(hr)
        for i = 1, #states - 1 do
            local tr = el("tr")
            tr:appendChild(text("td", states[i]))
            for j = 2, #states do
                local td = el("td")
                if j > i then
                    local k = pairkey(states[i], states[j])
                    local cb = document:createElement("input")
                    cb.type = "checkbox"
                    cb:addEventListener("change", function()
                        dirty(nil)()
                        rebuild_wit(pi)
                    end)
                    td:appendChild(cb)
                    rec.cells[k] = { td = td, cb = cb }
                end
                tr:appendChild(td)
            end
            tb:appendChild(tr)
        end
        box:appendChild(tb)
        box:appendChild(text("div", "distinguishing words:", "wlabel"))
        local wl = el("div")
        box:appendChild(wl)
        rec.witbox, rec.wit = wl, {}
        local r = el("div", "wordrow")
        r:appendChild(text("span", "equivalence classes:", "wlabel"))
        local cst = el("span", "st")
        local cinp = mk_input("expr", 40, dirty(cst))
        cinp.placeholder = "{q0,q3} {q1,q4} {q2} {q5}"
        r:appendChild(cinp); r:appendChild(cst)
        box:appendChild(r)
        rec.classes = cinp
        rec.cells["classes"] = { td = cst }
    elseif pv.kind == "cyk" then
        -- triangular X_{i,j} table: cell (i,j) covers the substring
        -- word[i..j]; bottom row repeats the word's letters
        local word = pv.word or ""
        local n = #word
        rec.cells = {}
        local tb = el("table", "trtable")
        local hr = el("tr")
        hr:appendChild(text("th", "X_{i,j}"))
        for j = 1, n do hr:appendChild(text("th", j)) end
        tb:appendChild(hr)
        for i = 1, n do
            local tr = el("tr")
            tr:appendChild(text("td", i))
            for j = 1, n do
                local td = el("td")
                if j >= i then
                    local inp = mk_input(nil, 9, dirty(st))
                    inp.placeholder = "-"
                    td:appendChild(inp)
                    rec.cells[i .. "," .. j] = { input = inp, td = td }
                end
                tr:appendChild(td)
            end
            tb:appendChild(tr)
        end
        local wr = el("tr")
        wr:appendChild(text("td", "w"))
        for j = 1, n do
            wr:appendChild(text("td", word:sub(j, j)))
        end
        tb:appendChild(wr)
        box:appendChild(tb)
    elseif pv.kind == "grammar" or pv.kind == "normalise"
        or pv.kind == "pda" or pv.kind == "tm" or pv.kind == "pattern"
        or (pv.kind == "tree" and (pv.count or 1) <= 1) then
        local r = el("div", "wordrow")
        local rst = el("span", "st")
        local ta = document:createElement("textarea")
        ta.className = "grammartext"
        ta:setAttribute("spellcheck", "false")
        ta.rows = pv.kind == "grammar" and 6
            or ((pv.kind == "pda" or pv.kind == "tm") and 8 or 3)
        ta.cols = 52
        ta.placeholder = pv.kind == "grammar" and
            "S -> aA | λ\nA -> bA | b"
            or (pv.kind == "pda" and
                "start: q0\nfinal: q1\nq0, a λ/A, q0\n"
                .. "q0, λ λ/λ, q1\nq1, b A/λ, q1"
            or (pv.kind == "tm" and
                "start: q0\nfinal: qf\nq0, a A R, q1\n"
                .. "q1, b b R, q1\nq1, B B L, qf"
                or (pv.kind == "tree" and "S(a b S(…) c c)"
                    or "(ab)^n c^m d^m c^n | n>=0, m>0")))
        local repl = (pv.kind == "grammar" or pv.kind == "normalise"
            or pv.kind == "pda") and GRAMMAR_REPLACE or TREE_REPLACE
        ta:addEventListener("input", function()
            replace_symbols(ta, repl)
            dirty(rst)()
        end)
        r:appendChild(ta); r:appendChild(rst)
        box:appendChild(r)
        if pv.hint then
            box:appendChild(text("div", pv.hint, "wlabel"))
        end
        rec.text, rec.expr_st = ta, rst
        rec.cells = { text = { td = rst } }
    elseif pv.kind == "derivation" or pv.kind == "tree" then
        rec.fields, rec.cells = {}, {}
        for d = 1, (pv.count or 1) do
            local r = el("div", "wordrow")
            if (pv.count or 1) > 1 then
                r:appendChild(text("span",
                    (pv.kind == "tree" and "tree #"
                     or "derivation #") .. d .. ":", "wlabel"))
            end
            local rst = el("span", "st")
            local ta = document:createElement("textarea")
            ta.className = "grammartext"
            ta:setAttribute("spellcheck", "false")
            ta.rows, ta.cols = 5, 52
            ta.placeholder = pv.kind == "tree"
                and "S(a b S(…) c c)" or
                ("S\nSAB\nAB\n…\n" .. (pv.target or ""))
            local repl = pv.kind == "tree" and TREE_REPLACE
                or DERIV_REPLACE
            ta:addEventListener("input", function()
                replace_symbols(ta, repl)
                dirty(rst)()
            end)
            r:appendChild(ta); r:appendChild(rst)
            box:appendChild(r)
            rec.fields[d] = ta
            rec.cells["d" .. d] = { td = rst }
        end
    elseif pv.kind == "cpump" then
        rec.cells, rec.cpump_i = {}, {}
        if pv.has_z then
            local r = el("div", "wordrow")
            r:appendChild(text("span", "z(k) =", "wlabel"))
            local inp = mk_input(22)
            if pv.z_hint then inp.placeholder = pv.z_hint end
            local rst = el("span", "st")
            inp:addEventListener("input", function()
                replace_symbols(inp, PUMP_REPLACE)
                dirty(rst)()
            end)
            r:appendChild(inp); r:appendChild(rst)
            box:appendChild(r)
            rec.cpump_z = inp
            rec.cells.z = { td = rst }
        end
        for i, c in ipairs(pv.cases or {}) do
            local r = el("div", "wordrow")
            r:appendChild(text("span", "case " .. i .. " — "
                .. c.desc, "wlabel"))
            box:appendChild(r)
            local r2 = el("div", "wordrow")
            r2:appendChild(text("span", "i =", "wlabel"))
            local inp = mk_input(10)
            local rst = el("span", "st")
            inp:addEventListener("input", dirty(rst))
            r2:appendChild(inp); r2:appendChild(rst)
            box:appendChild(r2)
            rec.cpump_i[i] = inp
            rec.cells["i" .. i] = { td = rst }
        end
    end
    return box
end

-- ---------- persistence (localStorage, keys "landm:<sheet>:<task>") ----------
local STORE_PREFIX = "landm:"
local function storage_key()
    local sh = cur_sheet()
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
    if state.view.type == "parts" then
        rec.parts = {}
        for pi,p in pairs(state.parts) do
            local pr = {}
            if p.kind == "aut" then
                pr.aut = p.app and landm_call("aut_state", p.app) or ""
                if p.re then pr.re = p.re.value end
            elseif p.kind == "trace" then
                pr.seqs = {}
                for wi,inp in ipairs(p.seqs) do pr.seqs[wi] = inp.value end
            elseif p.kind == "accept" then
                pr.ans = {}
                for wi,sel in ipairs(p.ans) do pr.ans[wi] = sel.value end
            elseif p.kind == "table" or p.kind == "stable"
                or p.kind == "cyk" then
                pr.cells = {}
                for k,c in pairs(p.cells) do pr.cells[k] = c.input.value end
            elseif p.kind == "closure" then
                pr.sets = {}
                for wi,inp in ipairs(p.sets) do pr.sets[wi] = inp.value end
            elseif p.kind == "regexp" then
                pr.expr = p.expr.value
            elseif p.kind == "grammar" or p.kind == "normalise"
                or p.kind == "pda" or p.kind == "tm"
                or p.kind == "pattern"
                or (p.kind == "tree" and not p.fields) then
                pr.text = p.text and p.text.value or ""
            elseif p.kind == "cpump" then
                pr.z = p.cpump_z and p.cpump_z.value or ""
                pr.is = {}
                for i, inp in ipairs(p.cpump_i or {}) do
                    pr.is[i] = inp.value
                end
            elseif p.kind == "derivation" or p.kind == "tree" then
                pr.texts = {}
                for d, ta in ipairs(p.fields or {}) do
                    pr.texts[d] = ta.value
                end
            elseif p.kind == "choice" then
                pr.sel = {}
                for k, sel in pairs(p.sels) do pr.sel[k] = sel.value end
            elseif p.kind == "pumping" then
                pr.z = p.z.value
                pr.k = p.ksel and p.ksel.value or nil
                pr.gen = p.gen and {
                    u = p.gen.u.value, v = p.gen.v.value,
                    w = p.gen.w.value, i = p.gen.i.value } or nil
                pr.is = {}
                for ri, inp in ipairs(p.i_inps) do pr.is[ri] = inp.value end
            elseif p.kind == "min_table" then
                pr.marks = {}
                for k, c in pairs(p.cells) do
                    if c.cb and c.cb.checked then pr.marks[#pr.marks+1] = k end
                end
                pr.classes = p.classes.value
                pr.wit = {}
                for k, inp in pairs(p.wit or {}) do pr.wit[k] = inp.value end
            end
            rec.parts[pi] = pr
        end
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
    if state.view.type == "parts" then
        for pi, pr in pairs(rec.parts or {}) do
            local p = state.parts[tonumber(pi)]
            if p then
                if p.kind == "aut" then
                    if p.app and type(pr.aut) == "string"
                       and pr.aut ~= "" then
                        landm_call("aut_load", p.app, pr.aut)
                        p.restored = true
                    end
                    if p.re and pr.re then p.re.value = pr.re end
                elseif p.kind == "trace" then
                    for wi,inp in ipairs(p.seqs) do
                        inp.value = (pr.seqs or {})[wi] or ""
                    end
                elseif p.kind == "accept" then
                    for wi,sel in ipairs(p.ans) do
                        sel.value = (pr.ans or {})[wi] or ""
                    end
                elseif p.kind == "table" or p.kind == "stable"
                    or p.kind == "cyk" then
                    for k,c in pairs(p.cells) do
                        c.input.value = (pr.cells or {})[k] or ""
                    end
                elseif p.kind == "closure" then
                    for wi,inp in ipairs(p.sets) do
                        inp.value = (pr.sets or {})[wi] or ""
                    end
                elseif p.kind == "regexp" then
                    if pr.expr then p.expr.value = pr.expr end
                elseif p.kind == "choice" then
                    for k, sel in pairs(p.sels) do
                        sel.value = (pr.sel or {})[k] or ""
                    end
                elseif p.kind == "pumping" then
                    if pr.z then p.z.value = pr.z end
                    if pr.k and p.ksel then p.ksel.value = pr.k end
                    p.pending_is = pr.is
                    p.pending_gen = pr.gen
                    if pr.z and pr.z:match("%S") then
                        request_splits(tonumber(pi))
                    end
                elseif p.kind == "min_table" then
                    local mk = {}
                    for _, k in ipairs(pr.marks or {}) do mk[k] = true end
                    for k, c in pairs(p.cells) do
                        if c.cb then c.cb.checked = mk[k] and true or false end
                    end
                    rebuild_wit(tonumber(pi))
                    for k, inp in pairs(p.wit) do
                        inp.value = (pr.wit or {})[k] or ""
                    end
                    if pr.classes then p.classes.value = pr.classes end
                elseif p.kind == "grammar" or p.kind == "normalise"
                    or p.kind == "pda" or p.kind == "tm"
                    or p.kind == "pattern"
                    or (p.kind == "tree" and not p.fields) then
                    if pr.text and p.text then
                        p.text.value = pr.text
                    end
                elseif p.kind == "derivation" or p.kind == "tree" then
                    for d, ta in ipairs(p.fields or {}) do
                        ta.value = (pr.texts or {})[d] or ""
                    end
                elseif p.kind == "cpump" then
                    if p.cpump_z and pr.z then
                        p.cpump_z.value = pr.z
                    end
                    for i, inp in ipairs(p.cpump_i or {}) do
                        inp.value = (pr.is or {})[i] or ""
                    end
                end
            end
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

-- ---------- part (a)(b)(c) sub-tabs: hide all but the active part.
-- Every part is rendered and booted (seeds/takeover/check-all reach
-- into sibling parts' editors); only visibility toggles.  The aut
-- canvas re-sizes itself via ResizeObserver on un-hide.
local function select_part(pi)
    state.part_i = pi
    for i,box in ipairs(state.part_boxes or {}) do
        box.style.display = (i == pi) and "" or "none"
    end
    for i,t in ipairs(state.part_tabs or {}) do
        t.className = (i == pi) and "parttab active" or "parttab"
    end
end

-- ---------- render dispatch ----------
local function render(view)
    state.view = view
    state.holes, state.st, state.free_blocks = {}, {}, {}
    state.parts = {}
    state.part_boxes, state.part_tabs, state.part_marks = {}, nil, {}
    state.part_i = 1
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
    if view.type == "parts" then
        checkbtn.textContent = "Check all"
        rulesbox_el.style.display = "none"
        if syntaxhint_el then
            syntaxhint_el.innerHTML = PARTS_SYNTAX_HINT
        end
        if view.given then
            proof_el:appendChild(render_given(view.given))
        end
        -- guided construction: stage id -> compose/simplify part
        -- indices, so seeds pull the stage's effective automaton and
        -- takeover finds its compose editor
        state.stage_map = {}
        for pi,pv in ipairs(view.parts or {}) do
            if pv.sid then
                local e = state.stage_map[pv.sid] or {}
                e.compose = pi
                state.stage_map[pv.sid] = e
            end
            if pv.takeover_from then
                local e = state.stage_map[pv.takeover_from] or {}
                e.simplify = pi
                state.stage_map[pv.takeover_from] = e
            end
        end
        -- a) b) c)… part tabs: one strip when the task has >1 part
        local nparts = #(view.parts or {})
        if nparts > 1 then
            local strip = el("div", "parttabs")
            state.part_tabs = {}
            for pi,pv in ipairs(view.parts) do
                local b = el("button", "parttab")
                b:appendChild(text("span",
                    pv.sub or (string.char(96 + pi) .. ")")))
                local mk = el("span", "ptmark")
                b:appendChild(mk)
                state.part_marks[pi] = mk
                b:addEventListener("click", function()
                    select_part(pi)
                end)
                state.part_tabs[pi] = b
                strip:appendChild(b)
            end
            proof_el:appendChild(strip)
        end
        for pi,pv in ipairs(view.parts or {}) do
            local box = render_part(pv, pi)
            state.part_boxes[pi] = box
            proof_el:appendChild(box)
        end
        boot_pending_aut()
        restore_local()
        -- first visit to a guided task: pre-place the locked given
        -- components so the canvas never starts bare; a non-empty
        -- (restored) model keeps the student's work instead
        local appids = {}
        for pi,pv in ipairs(view.parts or {}) do
            local p = state.parts[pi]
            if p and p.kind == "aut" and p.app then
                appids[#appids + 1] = p.app
            end
            if pv.seeds_locked and #pv.seeds_locked > 0 then
                -- restored work may still be in the app's pending
                -- queue when aut_state reads ""; never clobber it
                if p and not p.restored then
                    local s = p.app and landm_call("aut_state", p.app)
                    local ok, m = pcall(json.decode, s or "")
                    if not (ok and type(m) == "table"
                            and m.states and #m.states > 0) then
                        refresh_components(pi)
                    end
                end
            end
        end
        -- a restore can leave embedded components stale vs. the stage
        -- they came from: once every editor has applied its pending
        -- state, re-sync all guided components in stage order (upsert
        -- keeps positions, flags and student wiring — entry/exit
        -- edges retarget onto renamed successors)
        if #appids > 0 then
            landm_call("aut_when_ready", json.encode(appids), function()
                for pi,pv in ipairs(view.parts or {}) do
                    if pv.seeds_locked and #pv.seeds_locked > 0 then
                        refresh_components(pi)
                    end
                end
            end)
        end
        if nparts > 1 then select_part(state.part_i) end
        return
    end
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

send_check = function(only_pi)
    local view = state.view
    if not view then return end
    local data = { what="check", id=state.id, sections={} }
    if view.type == "regexp" then
        data.expr = state.regexp_input and state.regexp_input.value or ""
        util.js_post_message(json.encode(data))
        return
    end
    if view.type == "parts" then
        local parts = {}
        for pi,p in pairs(state.parts) do
            if not only_pi or pi == only_pi then
            local pd = { pi = pi }
            if p.kind == "aut" then
                pd.aut = p.app
                    and landm_call("aut_state", p.app) or ""
                if p.re then pd.re = p.re.value end
                local pvd = state.view.parts and state.view.parts[pi]
                if pvd and pvd.seeds_locked then
                    pd.seeds = {}
                    for _, t in ipairs(pvd.seeds_locked) do
                        local st = t:match("^[^#]+") or t
                        if not pd.seeds[st] then
                            local m = stage_aut_json(st)
                            if m then
                                pd.seeds[st] = json.encode(m)
                            end
                        end
                    end
                end
                if pvd and pvd.takeover_from then
                    local e = state.stage_map[pvd.takeover_from]
                    local cp = e and state.parts[e.compose]
                    pd.src = cp and cp.app
                        and landm_call("aut_state", cp.app) or ""
                end
            elseif p.kind == "trace" then
                pd.seqs = {}
                for wi,inp in ipairs(p.seqs) do
                    pd.seqs[wi] = inp.value
                end
            elseif p.kind == "accept" then
                pd.ans = {}
                for wi,sel in ipairs(p.ans) do
                    pd.ans[wi] = sel.value
                end
            elseif p.kind == "table" or p.kind == "stable"
                or p.kind == "cyk" then
                pd.cells = {}
                for k,c in pairs(p.cells) do
                    pd.cells[k] = c.input.value
                end
            elseif p.kind == "closure" then
                pd.sets = {}
                for wi,inp in ipairs(p.sets) do
                    pd.sets[wi] = inp.value
                end
            elseif p.kind == "regexp" then
                pd.expr = p.expr.value
            elseif p.kind == "choice" then
                pd.sel = {}
                for k, sel in pairs(p.sels) do pd.sel[k] = sel.value end
            elseif p.kind == "pumping" then
                pd.z = p.z.value
                pd.k = p.last_k or
                       (p.ksel and tonumber(p.ksel.value))
                pd.is = {}
                for ri, inp in ipairs(p.i_inps) do pd.is[ri] = inp.value end
                pd.gen = p.gen and {
                    u = p.gen.u.value, v = p.gen.v.value,
                    w = p.gen.w.value, i = p.gen.i.value } or nil
            elseif p.kind == "grammar" or p.kind == "normalise"
                or p.kind == "pda" or p.kind == "tm"
                or p.kind == "pattern"
                or (p.kind == "tree" and not p.fields) then
                pd.text = p.text and p.text.value or ""
            elseif p.kind == "cpump" then
                pd.z = p.cpump_z and p.cpump_z.value or ""
                pd.is = {}
                for i, inp in ipairs(p.cpump_i or {}) do
                    pd.is[i] = inp.value
                end
            elseif p.kind == "derivation" or p.kind == "tree" then
                pd.texts = {}
                for d, ta in ipairs(p.fields or {}) do
                    pd.texts[d] = ta.value
                end
            elseif p.kind == "min_table" then
                pd.marks = {}
                for k, c in pairs(p.cells) do
                    if c.cb and c.cb.checked then
                        pd.marks[#pd.marks+1] = k
                    end
                end
                pd.classes = p.classes.value
                pd.wit = {}
                for k, inp in pairs(p.wit or {}) do pd.wit[k] = inp.value end
            end
            parts[#parts+1] = pd
            -- the check can take seconds in the worker (bounded PDA/TM
            -- searches) — mark it so the page does not look dead
            if p.st then paint_st(p.st, "pending", "checking…") end
            local mk = state.part_marks and state.part_marks[pi]
            if mk then mk.className = "ptmark pending"
                      mk.textContent = "…" end
            end
        end
        data.parts = parts
        data.part = only_pi
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
    fail           = { "fail",   "✗" },
    warn           = { "warn",   "⚠" },
    noop           = { "fail",   "✗" },
    instance_fail  = { "fail",   "✗" },
    mismatch       = { "fail",   "✗" },
    endpoint       = { "fail",   "✗" },
    ih_unnecessary = { "warn",   "⚠" },
    pending        = { "pending","…" },
    missing_ih     = { "fail",   "✗" },
    parse          = { "fail",   "✗" },
    too_large      = { "fail",   "✗" },
    comp_missing   = { "fail",   "✗" },
    stale          = { "fail",   "✗" },
    boundary       = { "fail",   "✗" },
    composable     = { "fail",   "✗" },
    disconnected   = { "fail",   "✗" },
    empty          = { "pending","□" },
}

paint_st = function(st, kind, extra)
    local k = KIND[kind] or KIND.pending
    st.className = "st " .. k[1]
    st.innerHTML = ""
    st:appendChild(text("span", k[2], "stmark"))
    if extra then st:appendChild(text("span", "  " .. extra)) end
end

-- worker answered a "pump_splits" request: build the i-table
local function render_splits(pi, res)
    local p = state.parts[pi]
    if not (p and p.splitbox) then return end
    clear(p.splitbox)
    p.i_inps, p.row_st = {}, {}
    if res.err then
        paint_st(p.z_st, "fail", res.err)
        return
    end
    paint_st(p.z_st, "ok")
    p.splitbox:appendChild(text("div",
        "z(" .. tostring(res.k) .. ") = " .. res.word ..
        "  —  pick i ≠ 1 for every decomposition:", "wlabel"))
    local function lam(s) return s == "" and "λ" or s end
    for ri, s in ipairs(res.splits or {}) do
        local r = el("div", "wordrow")
        r:appendChild(text("span",
            "u = " .. lam(s.u) .. ",  v = " .. lam(s.v) ..
            ",  w = " .. lam(s.w), "wlabel"))
        local rst = el("span", "st")
        local inp = mk_input(nil, 4, dirty(rst))
        inp.placeholder = "i"
        r:appendChild(text("span", "i =", "wlabel"))
        r:appendChild(inp)
        local pv = el("span", "wlabel")
        inp:addEventListener("input", function()
            local n = tonumber(inp.value)
            pv.textContent = (n and n >= 0 and n == math.floor(n))
                and ("  →  " .. lam(s.u .. s.v:rep(n) .. s.w)) or ""
        end)
        r:appendChild(pv); r:appendChild(rst)
        p.splitbox:appendChild(r)
        p.i_inps[ri], p.row_st[ri] = inp, rst
    end
    -- the general decomposition (all k): only available when the
    -- first block of z(k) dominates the first-k window — then every
    -- legal split has v = sym^q for some 1 ≤ q ≤ k.  The student
    -- writes u, v, w themselves as patterns in the parameters
    -- (k, p, q).
    p.last_k = res.k
    local gen = res.gen or {}
    if gen.sym then
        p.splitbox:appendChild(text("div",
            "general decomposition (all k):  write u, v, w as "
            .. "patterns in the parameters — every legal split has "
            .. "u = " .. gen.sym .. "^p, v = " .. gen.sym .. "^q "
            .. "with p ≥ 0, q ≥ 1, p+q ≤ k.",
            "wlabel"))
        local pend = p.pending_gen or {}
        p.pending_gen = nil
        local gst = el("span", "st")
        local function grow(lab, ph, key)
            local gr = el("div", "wordrow")
            gr:appendChild(text("span", lab, "wlabel"))
            local inp = mk_input("expr", 20, dirty(gst))
            inp.placeholder = ph
            if pend[key] then inp.value = pend[key] end
            gr:appendChild(inp)
            p.splitbox:appendChild(gr)
            return inp
        end
        local u_inp = grow("u =", "e.g. a^p", "u")
        local v_inp = grow("v =", "e.g. a^q", "v")
        local w_inp = grow("w =", "e.g. a^{k-p-q}b^k", "w")
        local i_inp = grow("i(k,q) =", "e.g. 2, q+1, k+1", "i")
        p.splitbox:appendChild(gst)
        p.gen = { u = u_inp, v = v_inp, w = w_inp, i = i_inp }
        p.gen_st = gst
    elseif gen.err then
        p.splitbox:appendChild(text("div",
            "general decomposition: " .. gen.err, "wlabel"))
        p.gen = nil
    else
        p.gen = nil
    end
    if p.pending_is then
        for ri, v in pairs(p.pending_is) do
            if p.i_inps[tonumber(ri)] then
                p.i_inps[tonumber(ri)].value = v
            end
        end
        p.pending_is = nil
    end
end

local function row_st_el(si, ri)
    if state.view and state.view.free then
        local blk = state.free_blocks[si]
        return blk and blk.rows[ri] and blk.rows[ri].st
    end
    return state.st[si] and state.st[si][ri]
end

local function clear_part_st(p)
    if p.st then p.st.textContent=""; p.st.className="st" end
    for _,rst in pairs(p.row_st or {}) do
        rst.textContent=""; rst.className="st"
    end
    for _,c in pairs(p.cells or {}) do c.td.className = "" end
    if p.re_st then p.re_st.textContent=""; p.re_st.className="st" end
    if p.expr_st then
        p.expr_st.textContent=""; p.expr_st.className="st"
    end
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
    for _,p in pairs(state.parts or {}) do clear_part_st(p) end
end

local function paint(res)
    if res.partial then
        for _,pres in ipairs(res.parts or {}) do
            local p = state.parts[pres.pi]
            if p then clear_part_st(p) end
        end
    else
        clear_all_st()
    end
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
    if state.view and state.view.type == "parts" then
        for _,pres in ipairs(res.parts or {}) do
            local p = state.parts[pres.pi]
            if p then
                if pres.ok then
                    paint_st(p.st, "ok", pres.msg)
                elseif pres.msg then
                    paint_st(p.st, pres.kind or "fail", pres.msg)
                else
                    paint_st(p.st, pres.kind or "pending")
                end
                local mk = state.part_marks and state.part_marks[pres.pi]
                if mk then
                    local k = KIND[pres.ok and "ok"
                                   or (pres.msg and (pres.kind or "fail"))
                                   or (pres.kind or "pending")]
                             or KIND.pending
                    mk.className = "ptmark " .. k[1]
                    mk.textContent = k[2]
                end
                for wi,row in pairs(pres.rows or {}) do
                    local rst = p.row_st and p.row_st[tonumber(wi)]
                    if rst and row.kind and row.kind ~= "empty" then
                        paint_st(rst, row.kind,
                                 row.kind ~= "ok" and row.msg or nil)
                    end
                end
                for k,cr in pairs(pres.cells or {}) do
                    local c = p.cells and p.cells[k]
                    if c and c.td then
                        c.td.className =
                            cr.kind == "ok" and "cell-ok"
                            or cr.kind == "empty" and ""
                            or "cell-bad"
                    end
                end
                if pres.re and p.re_st then
                    if pres.re.ok then paint_st(p.re_st, "ok")
                    else paint_st(p.re_st, pres.re.kind or "mismatch",
                                  pres.re.msg) end
                end
                if pres.gen and p.gen_st then
                    paint_st(p.gen_st,
                             pres.gen.ok and "ok"
                             or pres.gen.kind or "mismatch",
                             pres.gen.msg)
                end
            end
        end
        if not res.partial then
            clear(summary_el)
            if res.ok then
                summary_el:appendChild(text("span",
                    "all parts verified ✓", "st ok"))
            else
                summary_el:appendChild(text("span",
                    res.msg or "not yet fully verified.", "st fail"))
            end
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
            if st then paint_st(st, "fail", sres.msg) end
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
    local sh = cur_sheet()
    local g = sh and sh.groups[state.group_i]
    local sub = g and g.subtasks[state.sub_i]
    if not sub then return nil end
    if sub.variants then
        local v = sub.variants[state.variant_i or 1]
        if v then return v.id end
    end
    if state.free and sub.free_id then return sub.free_id end
    return sub.id
end

local function select_task()
    local id = current_task_id()
    if id then request_view(id) end
end

local function render_tabs()
    clear(tabs_el); clear(subtabs_el)
    local sh = cur_sheet()
    if not sh then return end
    if not state.pinned and #sh.groups > 1 then
    for gi,g in ipairs(sh.groups) do
        local t = text("button", g.title,
            gi==state.group_i and "tab active" or "tab")
        t:addEventListener("click", function()
            state.group_i, state.sub_i = gi, 1
            state.variant_i = 1
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
            state.variant_i = 1
            render_tabs(); select_task()
        end)
        subtabs_el:appendChild(t)
    end
    -- variant toggle: guided vs free (per subtask, student chooses)
    clear(variant_el)
    local sub = g.subtasks[state.sub_i]
    if sub and sub.variants then
        variant_el:appendChild(text("span", "variant: ", "varlabel"))
        for vi,v in ipairs(sub.variants) do
            local b = text("button", v.label,
                (state.variant_i or 1)==vi and "vartab active"
                                           or "vartab")
            b:addEventListener("click", function()
                if (state.variant_i or 1) ~= vi then
                    state.variant_i = vi
                    render_tabs(); select_task()
                end
            end)
            variant_el:appendChild(b)
        end
    elseif sub and sub.free_id then
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
checkbtn:addEventListener("click", function() send_check() end)

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
    util.js_get("landm.download")(false, "landm-saved-work.json", dump)
    save_note("file downloaded — it contains every exercise on every sheet")
end)
loadfile_btn:addEventListener("click", function() loadinput:click() end)
loadinput:addEventListener("change", function()
    util.js_get("landm.read_file")(false, loadinput, import_and_reload)
    loadinput.value = ""
end)
loadtext_btn:addEventListener("click", function() import_and_reload(stateta.value) end)
savedetails_el:addEventListener("toggle", function()
    if savedetails_el.open then stateta.value = dump_all() or "" end
end)
-- NB: no js_post_message here — it is only wired after this module's
-- require() returns.  The worker pushes the task list itself on load.

-- bad ?exercise=/?sub= deep link: show an error + the valid choices
-- instead of silently landing on the default task
local function render_error(bad_ex, bad_sub)
    clear(proof_el); clear(summary_el)
    clear(ihrow_el); clear(rulesbox_el)
    clear(variant_el)
    checkbtn.textContent = "Check"
    goal_el.innerHTML = ""
    goal_el:appendChild(text("span", "Exercise not found", "goaltitle"))
    local msg = el("div", "desc")
    if bad_ex then
        msg.textContent = "There is no exercise \xE2\x80\x9C" .. bad_ex
            .. "\xE2\x80\x9D on this site.  Available exercises:"
    else
        msg.textContent = "There is no part \xE2\x80\x9C" .. bad_sub
            .. "\xE2\x80\x9D in this exercise.  Available parts:"
    end
    proof_el:appendChild(msg)
    local row = el("div", "exlinks")
    if bad_ex then
        for _,sh in ipairs(state.sheets) do
            for _,g in ipairs(sh.groups) do
                local a = el("a", "exlink")
                a.href = "?exercise=" .. g.id
                a.textContent = g.id
                row:appendChild(a)
            end
        end
    else
        local g = cur_sheet().groups[state.group_i]
        for _,sub in ipairs(g.subtasks) do
            local a = el("a", "exlink")
            a.href = "?exercise=" .. g.id .. "&sub=" .. sub.sub
            a.textContent = sub.sub .. ")"
            row:appendChild(a)
        end
    end
    proof_el:appendChild(row)
end

-- ---------- message handler (worker -> gui) ----------
return function(data)
    local ok,msg = pcall(json.decode, data)
    if not ok then return end
    data = msg
    if data.what == "tasks" then
        state.sheets = data.sheets
        local bad_ex, bad_sub
        if ex_param then
            for si,sh in ipairs(state.sheets) do
                for gi,g in ipairs(sh.groups) do
                    if g.id == ex_param then
                        state.sheet_i, state.group_i = si, gi
                        state.pinned = true
                        break
                    end
                end
                if state.pinned then break end
            end
            if not state.pinned then bad_ex = ex_param end
        end
        if sub_param and not bad_ex then
            local g = cur_sheet().groups[state.group_i]
            local found = false
            for si,sub in ipairs(g.subtasks) do
                if sub.sub == sub_param then
                    state.sub_i = si
                    found = true
                    break
                end
            end
            if not found then bad_sub = sub_param end
        end
        render_tabs()
        if bad_ex or bad_sub then
            render_error(bad_ex, bad_sub)
        else
            select_task()
        end
    elseif data.what == "view" then
        if data.id == state.id then render(data.view) end
    elseif data.what == "splits" then
        if data.id == state.id then
            render_splits(data.pi, data.res or {})
        end
    elseif data.what == "result" then
        if data.id == state.id then paint(data.res) end
    end
end
