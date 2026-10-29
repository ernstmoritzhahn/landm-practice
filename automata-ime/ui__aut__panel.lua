-- ui/aut/panel.lua -- the automaton editor's property column content:
-- "State" (name, initial, accepting, delete) for G.selected and
-- "Transition" (label, delete) for G.sel_edge.  Rendered as plain rows
-- inside the right-hand "aut_props" group of aut.frame's resizable
-- split (same column idiom as the BayesL properties panels); G.panel
-- carries the column rect so canvas gestures stay out of it.

local ffi   = require "ffi"
local A     = require "ui.api"
local util  = require "ui.util"
local gen   = require "ui.gen"
local G     = require "ui.aut.state"
local model = require "ui.aut.model"
local net   = require "ui.aut.net"
local hist  = require "ui.aut.history"
local sim   = require "ui.aut.sim"
local checks = require "server.checks"

local set_str = util.set_str
local NK = gen.NK
local NKL = gen.NKL
local TH  = gen.THEME
local col = util.col
local pk  = util.pk
local in_rect = util.in_rect

local f4 = ffi.new("float[4]")
local f2 = ffi.new("float[2]")
local C_CLEAR = {0, 0, 0, 0}

local name_buf  = ffi.new("char[64]")
local label_buf = ffi.new("char[128]")
local alpha_buf = ffi.new("char[128]")
local alpha_for = nil      -- alphabet text the buffer currently holds
local panel_for = nil      -- selection id the buffers currently mirror

local C_RED   = {200, 40, 40}
local C_AMBER = {200, 165, 0}
local C_HINT  = {115, 118, 126}

-- transition-label grammar per machine type, shown under the edit
-- field while a transition is selected — the string the hosting page
-- used to print below the canvas
local LABEL_HINTS = {
    dfa = "comma list of symbols, e.g. a,b",
    nfa = "comma list of symbols, e.g. a,b",
    ["dfa-part"] = "comma list of symbols, e.g. a,b",
    ["nfa-eps"] = "comma list of symbols, e.g. a,b "
        .. "\xc2\xb7 \\lambda completes to \xce\xbb (\xce\xb5-move)",
    pda = "'input pop/push', e.g. a A/AA or \xce\xbb Z/\xce\xbb "
        .. "\xc2\xb7 several clauses on one edge via ; or , "
        .. "\xc2\xb7 \xce\xbb = no read/pop/push "
        .. "\xc2\xb7 a push may be a string",
    tm  = "'read write move', move \xe2\x88\x88 {L,R,S}, e.g. a A R "
        .. "\xc2\xb7 \xe2\x8a\x94 = blank "
        .. "\xc2\xb7 ~ = keep symbol",
}
local function label_hint()
    local t = G.aut_type or "nfa"
    local nt = t:match("^n?tm%-(%d+)$")
    if nt then
        return "one 'read write move' clause per tape, | separates "
            .. "tapes \xc2\xb7 " .. nt
            .. " tapes, e.g. a a R | \xe2\x8a\x94 X S"
    end
    return LABEL_HINTS[t]
        or (t:match("^d?pda") and LABEL_HINTS.pda)
        or (t:match("^ntm") and LABEL_HINTS.tm)
end

local aut_panel = {}

-- state-changing edits MUST go through model.on_changed, not plain
-- net.dirty: ui.lua wraps on_changed to count student edits for
-- sendDataToExternal (autosave, guided-component sync, Anubis), and a
-- bare net.dirty() only revalidates — the change would be invisible
-- until the student clicked something else.  Applies per keystroke:
-- label/name/alphabet fields write the model every frame.
local function changed()
    if model.on_changed then model.on_changed() else net.dirty() end
end

local function edit_field(buf, max)
    local ev = A.edit_zt(NK.EDIT_FIELD |
                         (G.readonly and NK.EDIT_READ_ONLY or 0),
                         buf, max)
    -- NK_EDIT_INACTIVE (2) is reported every frame a panel is open —
    -- only ACTIVE means the field actually owns the keyboard
    if util.hasflag(ev, NK.EDIT_ACTIVE) then G.edit_seen = true end
    return ev
end

-- locked selection (given component in guided composition): the
-- structure is fixed — name and transitions are read-only — but
-- initial/accepting are wiring decisions, so their toggles stay live
local function state_panel_locked(n)
    A.row(20, 1); A.label("State " .. n.name, NK.TEXT_LEFT)
    A.row(20, 1); A.label("given component (locked)", NK.TEXT_LEFT)
    if n.seed_entry then
        A.row(20, 1); A.label("dashed arrow: component's entry",
                              NK.TEXT_LEFT)
    end
    if n.seed_exit then
        A.row(20, 1); A.label("dashed ring: component's exit",
                              NK.TEXT_LEFT)
    end
    A.row(24, 1)
    if A.button(n.initial and "Initial: yes" or "Initial: no") ~= 0
       and not G.readonly then
        if not n.initial then model.set_initial(G, G.selected) end
    end
    A.row(24, 1)
    if A.button(n.accepting and "Accepting: yes" or "Accepting: no")
       ~= 0 and not G.readonly then
        model.toggle_accepting(G, G.selected)
    end
    A.row(24, 1)
    if A.button("Close") ~= 0 then G.selected = nil end
end

local function state_panel()
    local n = G.nodes[G.selected]
    if not n then G.selected = nil return end
    if n.locked then state_panel_locked(n) return end
    if panel_for ~= n.id then
        panel_for = n.id
        set_str(name_buf, n.name)
    end
    A.row(20, 1); A.label("State", NK.TEXT_LEFT)
    A.row(20, 1); A.label("Name", NK.TEXT_LEFT)
    A.row(26, 1); edit_field(name_buf, 63)
    local nm = ffi.string(name_buf)
    if nm ~= "" and nm ~= n.name then
        n.name = nm
        G.nodes_ver = G.nodes_ver + 1
        changed()
    end
    -- one toggle per row: two columns clip at the column's ~200px
    A.row(24, 1)
    if A.button(n.initial and "Initial: yes" or "Initial: no") ~= 0
       and not G.readonly then
        if not n.initial then model.set_initial(G, G.selected) end
    end
    A.row(24, 1)
    if A.button(n.accepting and "Accepting: yes" or "Accepting: no")
       ~= 0 and not G.readonly then
        model.toggle_accepting(G, G.selected)
    end
    A.row(24, 2)
    if A.button("Delete") ~= 0 and not G.readonly then
        local i = G.selected
        G.selected = nil
        model.remove_state(G, i)
        return
    end
    if A.button("Close") ~= 0 then
        G.selected = nil
    end
end

local function edge_panel()
    local e = G.edges[G.sel_edge]
    if not e then G.sel_edge = nil return end
    local a, b = model.find_state(G, e.from), model.find_state(G, e.to)
    if not (a and b) then G.sel_edge = nil return end
    if e.locked then
        A.row(20, 1); A.label("Transition", NK.TEXT_LEFT)
        A.row(20, 1)
        A.label(string.format("%s \226\134\146 %s : %s",
                              G.nodes[a].name, G.nodes[b].name, e.label),
                NK.TEXT_LEFT)
        A.row(20, 1); A.label("given component (locked)", NK.TEXT_LEFT)
        A.row(24, 1)
        if A.button("Close") ~= 0 then G.sel_edge = nil end
        return
    end
    if panel_for ~= -e.id then
        panel_for = -e.id   -- edges share the buffer space, keyed <0
        set_str(label_buf, e.label)
    end
    A.row(20, 1); A.label("Transition", NK.TEXT_LEFT)
    A.row(20, 1)
    A.label(string.format("%s \226\134\146 %s",  -- "→"
                          G.nodes[a].name, G.nodes[b].name),
            NK.TEXT_LEFT)
    A.row(26, 1); edit_field(label_buf, 127)
    -- \lambda completes to the unicode symbol as you type — that's
    -- how epsilon transitions are entered (an empty label is an
    -- error, not lambda)
    local lb = ffi.string(label_buf)
    local cur = A.edit_cursor and A.edit_cursor() or -1
    local cv, nc = util.sub_track_cursor(lb, cur, "\\lambda", "\xce\xbb")
    cv, nc = util.sub_track_cursor(cv, nc, "\\lamda", "\xce\xbb")
    if cv ~= lb then
        set_str(label_buf, cv); lb = cv
        if A.edit_set_cursor and nc >= 0 then A.edit_set_cursor(nc) end
    end
    if lb ~= e.label then e.label = lb; changed() end
    local hint = label_hint()
    if hint then
        local fh = A.font_height and A.font_height() or 20
        A.text_color(util.pk(C_HINT))
        for ln in util.wrap_text(hint, math.max(
                (G.panel.w or 0) - 22, 60)):gmatch("[^\n]+") do
            A.row(fh + 4, 1)
            A.label(ln, NK.TEXT_LEFT)
        end
        A.text_color(util.pk(gen.THEME.BLACK))
    end
    A.row(24, 2)
    if A.button("Delete") ~= 0 and not G.readonly then
        local i = G.sel_edge
        G.sel_edge = nil
        model.remove_edge(G, i)
        return
    end
    if A.button("Close") ~= 0 then
        G.sel_edge = nil
    end
end

-- the declared alphabet is shared: it scopes the automaton's label
-- checks AND the expression's symbol membership (and feeds the
-- workspace's symbol buttons in re mode)
local stack_buf = ffi.new("char[128]")
local stack_for = nil
local function alphabet_field()
    A.row(20, 1); A.label("Alphabet (e.g. a,b)", NK.TEXT_LEFT)
    if alpha_for ~= G.alphabet then
        alpha_for = G.alphabet
        set_str(alpha_buf, G.alphabet or "")
    end
    A.row(26, 1); edit_field(alpha_buf, 127)
    local al = ffi.string(alpha_buf)
    if al ~= (G.alphabet or "") then
        G.alphabet = al
        changed()
    end
    -- PDA types carry a second alphabet for stack symbols
    if (G.aut_type or ""):match("^d?pda") then
        A.row(20, 1); A.label("Stack alphabet (e.g. A,Z)",
                              NK.TEXT_LEFT)
        if stack_for ~= G.stack_alphabet then
            stack_for = G.stack_alphabet
            set_str(stack_buf, G.stack_alphabet or "")
        end
        A.row(26, 1); edit_field(stack_buf, 127)
        local sl = ffi.string(stack_buf)
        if sl ~= (G.stack_alphabet or "") then
            G.stack_alphabet = sl
            changed()
        end
    end
end

-- hand-drawn checkbox + disclosure rows: the bridge exposes no
-- nk_check_label, so box, check and triangle are painted with the
-- canvas primitives and the whole row is the click target (same
-- idiom as chrome.lua's drawn rows)
local function hover_row(bx, by, bw, bh)
    A.mouse_pos(f2)
    if in_rect(f2[0], f2[1], {x = bx, y = by, w = bw, h = bh}) then
        if A.set_cursor then A.set_cursor(NKL.CURSOR_HAND, 0) end
        return true
    end
    return false
end

local function check_row(text, on, disabled)
    A.row(20, 1)
    if disabled then A.disable_begin() end
    local clicked = A.check(text, on and 1 or 0) ~= 0
    if disabled then A.disable_end() end
    return clicked
end

local function disclosure_row(text, open)
    A.row(20, 1)
    if A.widget(f4) == NK.WIDGET_INVALID then return false end
    local bx, by, bw, bh = f4[0], f4[1], f4[2], f4[3]
    local buf = A.canvas()
    if hover_row(bx, by, bw, bh) then
        A.fill_rect(buf, bx, by, bw, bh, 0.0, col(TH.GREY_XLIGHT))
    end
    local s = 5
    local cx, cy = bx + 8, by + bh * 0.5
    local r, g, b, a = col(TH.GREY_DARK)
    if open then
        A.fill_triangle(buf, cx - s, cy - s * 0.5,
                        cx + s, cy - s * 0.5, cx, cy + s,
                        r, g, b, a)
    else
        A.fill_triangle(buf, cx - s * 0.5, cy - s,
                        cx - s * 0.5, cy + s, cx + s, cy,
                        r, g, b, a)
    end
    local fh = A.font_height()
    A.draw_text(buf, bx + 20, by + (bh - fh) * 0.5,
                math.max(1, bw - 22), fh, text, #text,
                pk(C_CLEAR), pk(TH.BLACK))
    return A.press_in_rect(bx, by, bw, bh) ~= 0
end

-- one toggle per check that applies to the current mode — the same
-- modes filter the server driver applies, so irrelevant checks are
-- not just muted but absent.  The bar collapses to a single header
-- line ("▸ Checks (k/n on)") so it does not eat panel space; an
-- "all" row toggles every applicable check at once.  The problem
-- list below it keeps showing whichever checks are on.
local function checks_list()
    G.checks = G.checks or checks.defaults()
    local mode = G.mode or "aut"
    local function in_mode(s)
        return s.modes and s.modes[mode]
               or (not s.modes and mode == "aut")
    end
    local n_app, n_on = 0, 0
    for _, s in ipairs(checks.specs) do
        if in_mode(s) then
            n_app = n_app + 1
            if G.checks[s.key] ~= false then n_on = n_on + 1 end
        end
    end
    if disclosure_row("Checks (" .. n_on .. "/" .. n_app .. " on)",
                      G.checks_open) then
        G.checks_open = not G.checks_open
    end
    if not G.checks_open then return end
    if check_row("all", n_on == n_app, G.readonly) then
        local on = n_on < n_app
        for _, s in ipairs(checks.specs) do
            if in_mode(s) then G.checks[s.key] = on end
        end
        changed()
    end
    for _, s in ipairs(checks.specs) do
        if in_mode(s) then
            local on = G.checks[s.key] ~= false
            if check_row(s.name, on, G.readonly) then
                G.checks[s.key] = not on
                changed()
            end
        end
    end
end

-- automaton configuration: type cycle only; alphabet + checks are
-- emitted separately so the re column can share them
local function config_section()
    A.row(20, 1); A.label("Automaton", NK.TEXT_LEFT)
    A.row(24, 1)
    -- type selector (a dropdown: the family is too big for a cycle
    -- button).  Finite types, then the PDA family — plain = the
    -- lecture's L(M) accepting by final state AND empty stack, the
    -- -f/-e suffixes single out L_F/L_E, dpda* are the deterministic
    -- variants — then the TM family (det tm*, nondet ntm*).  Only
    -- NFA-λ admits lambda transitions; "partial" is the explicitly
    -- incomplete DFA variant.
    local TYPE_ORDER = {"nfa", "nfa-eps", "dfa", "dfa-part",
                        "pda", "pda-f", "pda-e",
                        "dpda", "dpda-f", "dpda-e",
                        "tm", "tm-2", "ntm", "ntm-2"}
    local TYPE_TEXT = {nfa = "NFA", ["nfa-eps"] = "NFA-\xce\xbb",
                       dfa = "DFA", ["dfa-part"] = "Partial DFA",
                       pda = "PDA", ["pda-f"] = "PDA, final state",
                       ["pda-e"] = "PDA, empty stack",
                       dpda = "DPDA",
                       ["dpda-f"] = "DPDA, final state",
                       ["dpda-e"] = "DPDA, empty stack",
                       tm = "TM", ["tm-2"] = "2-tape TM",
                       ntm = "NTM", ["ntm-2"] = "2-tape NTM"}
    local function type_text(ty)
        return TYPE_TEXT[ty]
            or ty:match("^tm%-(%d+)$") and (ty:match("^tm%-(%d+)$")
                                          .. "-tape TM")
            or ty:match("^ntm%-(%d+)$") and (ty:match("^ntm%-(%d+)$")
                                           .. "-tape NTM")
            or ty:upper()
    end
    local t = G.aut_type or "nfa"
    local items = {}
    for i, ty in ipairs(TYPE_ORDER) do items[i] = TYPE_TEXT[ty] end
    local picked = A.combo_label("Type: " .. type_text(t),
                                 table.concat(items, "\n"), 10,
                                 #items, 24, 0, 0)
    if picked >= 0 and picked < #items and not G.readonly then
        local nt = TYPE_ORDER[picked + 1]
        if nt ~= t then
            G.aut_type = nt
            changed()
        end
    end
end

-- read-only view (given diagrams, Anubis review): the panel becomes
-- pure inspection — labels only, no edit widgets, no toggles
local function state_panel_ro()
    local n = G.nodes[G.selected]
    if not n then G.selected = nil return end
    A.row(20, 1); A.label("State " .. n.name, NK.TEXT_LEFT)
    if n.initial then
        A.row(20, 1); A.label("initial state", NK.TEXT_LEFT)
    end
    if n.accepting then
        A.row(20, 1); A.label("accepting", NK.TEXT_LEFT)
    end
    A.row(24, 1)
    if A.button("Close") ~= 0 then G.selected = nil end
end

local function edge_panel_ro()
    local e = G.edges[G.sel_edge]
    if not e then G.sel_edge = nil return end
    local a, b = model.find_state(G, e.from), model.find_state(G, e.to)
    if not (a and b) then G.sel_edge = nil return end
    A.row(20, 1); A.label("Transition", NK.TEXT_LEFT)
    A.row(20, 1)
    A.label(string.format("%s \226\134\146 %s : %s",
                          G.nodes[a].name, G.nodes[b].name, e.label),
            NK.TEXT_LEFT)
    A.row(24, 1)
    if A.button("Close") ~= 0 then G.sel_edge = nil end
end

-- undo/redo/clear: model-level actions as a 3-button row; Clear asks
-- for inline confirmation (no modal popup exists in the bridge) before
-- wiping every editable component in one undoable step
local function editbar()
    A.row(22, 3)
    if A.button("Undo") ~= 0 and not G.readonly then hist.undo(G) end
    if A.button("Redo") ~= 0 and not G.readonly then hist.redo(G) end
    if A.button("Clear") ~= 0 and not G.readonly then
        G.confirm_clear = true
    end
    if G.confirm_clear then
        A.row(22, 2)
        if A.button("Really clear?") ~= 0 and not G.readonly then
            model.clear(G)
            G.confirm_clear = nil
        end
        if A.button("Cancel") ~= 0 then G.confirm_clear = nil end
    end
end

local function problems_section()
    local ps = G.problems
    if not ps or #ps == 0 then return end
    A.row(20, 1)
    A.label(string.format("Problems (%d)", #ps), NK.TEXT_LEFT)
    for i = 1, math.min(#ps, 40) do
        local p = ps[i]
        A.row(20, 1)
        A.text_color(util.pk(p.sev == "error" and C_RED or C_AMBER))
        A.label(p.msg or p.key or "problem", NK.TEXT_LEFT)
    end
    A.text_color(util.pk(gen.THEME.BLACK))
    if #ps > 40 then
        A.row(20, 1); A.label("…", NK.TEXT_LEFT)
    end
end

function aut_panel.draw()
    -- read-only: nothing in this column may look editable — states and
    -- transitions show their properties as plain labels; the
    -- mode/type/alphabet/checks sections stay hidden entirely
    if G.readonly then
        if G.selected then state_panel_ro()
        elseif G.sel_edge then edge_panel_ro()
        else
            panel_for = nil
            A.row(20, 1)
            A.label("read-only view", NK.TEXT_LEFT)
        end
        return
    end
    -- exam mode: the task fixed mode/type/alphabet — the only
    -- interactive widget left is the selection editor, which always
    -- sits on top.  When the task makes the checks editable
    -- (practice site), the collapsible toggle bar follows; problem
    -- warnings (whichever checks are on) go underneath.
    if G.exam then
        if G.selected then
            state_panel()
        elseif G.sel_edge then
            edge_panel()
        else
            panel_for = nil
            A.row(20, 1)
            A.label("Select state or transition", NK.TEXT_LEFT)
        end
        editbar()
        if G.checks_editable then checks_list() end
        problems_section()
        sim.section(disclosure_row)
        return
    end
    -- the mode toggle heads the column: automaton vs regular
    -- expression, one or the other per exercise
    local is_re = G.mode == "re"
    A.row(24, 1)
    if A.button("Mode: " .. (is_re and "Expression" or "Automaton"))
       ~= 0 and not G.readonly then
        G.mode = is_re and "aut" or "re"
        G.selected, G.sel_edge = nil, nil
        changed()
    end
    -- the selection editor always sits on top of the column — the
    -- exercise settings (mode/type/alphabet/checks) and problem
    -- warnings go underneath
    if G.selected then
        state_panel()
    elseif G.sel_edge then
        edge_panel()
    else
        panel_for = nil
    end
    if not is_re and not G.selected and not G.sel_edge then
        A.row(20, 1)
        A.label("Select state or transition", NK.TEXT_LEFT)
    end
    if not is_re then editbar() end
    if is_re then
        alphabet_field()
        checks_list()
        problems_section()
        return
    end
    config_section()
    alphabet_field()
    checks_list()
    problems_section()
    sim.section(disclosure_row)
end

return aut_panel
