-- ui/aut/sim.lua -- word simulator for the automaton under edit.
-- Students step (or run) an input word through the machine while the
-- canvas marks the live configurations' states (and the transitions
-- just taken).  Semantics mirror the grader's word_problem_* modules:
--
--   finite    conf (q, rest-word); one successor per matching edge —
--             comma labels act as parallel transitions; NFA-λ also
--             offers ε-moves (always, even mid-word)
--   pda       conf (q, rest, stack) with the stack's TOP on the left;
--             a clause 'input pop/push' fires on (read or ε) × (pop or
--             λ); push strings land first-char-on-top.  The pda family
--             (pda|pda-f|pda-e nondet, dpda* deterministic) shares the
--             stepping; only acceptance differs: plain types want
--             word AND stack empty in an accepting state, -f types
--             only the accepting state (L_F), -e types only the empty
--             stack (L_E — the lecture requires a NON-EMPTY
--             computation, so the steps counter must be > 0)
--   tm/tm-N   conf (q, tapes, heads); right/left-infinite tapes of
--             blanks (⊔ shown, stored "B"); '~'/λ write = keep; the
--             input word sits on tape 1; a halted accepting config
--             accepts (halt-in-accept, JFLAP-style).  ntm/ntm-N are
--             the nondeterministic variants — same stepping, more
--             successors per config
--
-- Nondeterminism is breadth-expanded per STEP press; identical
-- configurations merge and already-seen ones are dropped (a repeated
-- config can only loop).  Config count and total steps are capped so
-- a runaway branch cannot wedge the frame loop.
--
-- The section is opt-in per task payload (t.sim): the practice site
-- enables it, Anubis exams omit the flag.  Standalone defaults on.

local ffi  = require "ffi"
local A    = require "ui.api"
local util = require "ui.util"
local gen  = require "ui.gen"
local G    = require "ui.aut.state"

local has_ll, ll = pcall(require, "automata.label_lang")
if not has_ll then ll = nil end

local NK  = gen.NK
local TH  = gen.THEME
local pk  = util.pk
local set_str = util.set_str

local f4 = ffi.new("float[4]")

local C_GREEN  = {30, 140, 70}
local C_RED    = {200, 40, 40}
local C_AMBER  = {200, 165, 0}
local C_HINT   = {115, 118, 126}

local MAX_CONFS = 128     -- live configuration cap per step
local MAX_STEPS = 400     -- run cap
local PREVIEW   = 6       -- config lines shown

local sim = {}

local function trim(s)
    return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

local function is_lam(tk)
    return tk == "\xce\xbb" or tk == "\xce\xb5"
           or tk == "eps" or tk == "\\lambda" or tk == "\\lamda"
end

-- type-family predicates, local so the sim still branches correctly
-- when label_lang is absent (the structured labels then parse to
-- nothing, but the conf machinery stays consistent)
local function is_pda(t) return (t or ""):match("^d?pda") ~= nil end
-- pda acceptance mode: "fe" (final state AND empty stack — the
-- lecture's L(M)) | "f" (L_F) | "e" (L_E, non-empty computation)
local function pda_accept(t)
    local s = (t or ""):match("%-(%l+)$")
    return (s == "f" or s == "e") and s or "fe"
end

-- word string -> symbol list: greedy longest-match against the
-- declared alphabet (multi-char symbols exist, e.g. "10"), plain
-- characters otherwise.  Spaces and λ are skipped.
local function tokenize(word)
    local syms = {}
    for s in (G.alphabet or ""):gmatch("[^,]+") do
        s = trim(s)
        if s ~= "" then syms[#syms + 1] = s end
    end
    table.sort(syms, function(a, b) return #a > #b end)
    local toks, i = {}, 1
    while i <= #word do
        local hit
        for _, s in ipairs(syms) do
            if word:sub(i, i + #s - 1) == s then hit = s break end
        end
        if hit then
            toks[#toks + 1] = hit
            i = i + #hit
        else
            -- one UTF-8 codepoint as fallback symbol (alphabets can
            -- hold unicode symbols); λ/ε in the input are not read
            local b = word:byte(i)
            local n = b < 0x80 and 1 or (b < 0xE0 and 2
                      or (b < 0xF0 and 3 or 4))
            local c = word:sub(i, i + n - 1)
            i = i + n
            if c ~= " " and c ~= "" and not is_lam(c) then
                toks[#toks + 1] = c
            end
        end
    end
    return toks
end

-- editor model -> sim machine: tr[from] = list of {to, eid, syms/eps}
-- for finite types or {to, eid, cs = clause list} for pda/tm
local function build()
    local m = {type = G.aut_type or "nfa", tr = {}, errs = {},
               names = {}, acc = {}, initial = nil, lbl = {}}
    m.tapes = ll and ll.tapes(m.type)
           or ((m.type == "tm" or m.type == "ntm") and 1 or nil)
    for _, n in ipairs(G.nodes) do
        m.names[n.id] = n.name
        if n.initial then m.initial = n.id end
        if n.accepting then m.acc[n.id] = true end
    end
    for _, e in ipairs(G.edges) do
        local L = m.tr[e.from] or {}
        m.tr[e.from] = L
        m.lbl[e.id] = e.label
        if is_pda(m.type) or m.tapes then
            if ll then
                local cs, why = ll.parse_many(m.type, e.label)
                if cs then
                    L[#L + 1] = {to = e.to, eid = e.id, cs = cs}
                else
                    m.errs[#m.errs + 1] = string.format(
                        "%s: %s", e.label ~= "" and e.label or "?",
                        tostring(why))
                end
            elseif not m.ll_err then
                -- without the label grammar the machine silently
                -- had zero transitions — report once instead of
                -- rejecting every word for no visible reason
                m.ll_err = true
                m.errs[#m.errs + 1] =
                    "label grammar unavailable"
            end
        else
            local syms, eps, sl = {}, false, {}
            for tk in (e.label or ""):gmatch("[^,]+") do
                tk = trim(tk)
                if tk ~= "" then
                    if is_lam(tk) then eps = true
                    elseif not syms[tk] then
                        syms[tk] = true
                        sl[#sl + 1] = tk
                    end
                end
            end
            if not next(syms) and not eps then
                m.errs[#m.errs + 1] = "empty label"
            elseif eps and m.type ~= "nfa-eps" then
                m.errs[#m.errs + 1] =
                    "\xce\xbb only allowed for NFA-\xce\xbb"
            end
            L[#L + 1] = {to = e.to, eid = e.id, syms = syms, sl = sl,
                         eps = eps and m.type == "nfa-eps"}
        end
    end
    return m
end

-- ---------- configuration stepping ---------------------------------

local function conf_key(m, c)
    if m.tapes then
        local parts = {tostring(c.st)}
        for i = 1, m.tapes do
            parts[#parts + 1] = tostring(c.heads[i])
            local cells = {}
            for k, v in pairs(c.tapes[i]) do
                cells[#cells + 1] = tostring(k) .. "=" .. v
            end
            table.sort(cells)
            parts[#parts + 1] = table.concat(cells, ";")
        end
        return table.concat(parts, "|")
    elseif is_pda(m.type) then
        return tostring(c.st) .. "@" .. c.pos .. "|"
            .. table.concat(c.stack)
    end
    return tostring(c.st) .. "@" .. c.pos
end

-- successors of one config (and whether it can move at all)
local function succs(m, run, c, out, eids)
    if m.tapes then
        for _, t in ipairs(m.tr[c.st] or {}) do
            for _, ts in ipairs(t.cs) do
                local ok = true
                for i = 1, m.tapes do
                    if (c.tapes[i][c.heads[i]] or "B") ~= ts[i][1] then
                        ok = false break
                    end
                end
                if ok then
                    local tapes, heads = {}, {}
                    for i = 1, m.tapes do
                        local tp = {}
                        for k, v in pairs(c.tapes[i]) do tp[k] = v end
                        if ts[i][2] ~= nil then
                            tp[c.heads[i]] = ts[i][2]
                        end
                        tapes[i] = tp
                        local d = ts[i][3]
                        heads[i] = c.heads[i]
                            + (d == "L" and -1 or d == "R" and 1 or 0)
                    end
                    out[#out + 1] = {st = t.to, tapes = tapes,
                                     heads = heads}
                    eids[#eids + 1] = t.eid
                end
            end
        end
        return
    end
    local sym = run.toks[c.pos]
    if is_pda(m.type) then
        for _, t in ipairs(m.tr[c.st] or {}) do
            for _, cl in ipairs(t.cs) do
                -- (read|λ) × (pop|λ): input "" never reads, otherwise
                -- the clause symbol must be next; pop "" never pops,
                -- otherwise it must equal the stack top (stack[1])
                local rd = (cl.input == "" and 0)
                        or (sym ~= nil and cl.input == sym and 1)
                if rd and (cl.pop == "" or c.stack[1] == cl.pop) then
                    local ns, j = {}, 1
                    if cl.push ~= "" then
                        -- stack[1] is the top: a push string lands
                        -- FIRST-character-on-top (grader order)
                        for i = 1, #cl.push do
                            ns[j] = cl.push:sub(i, i)
                            j = j + 1
                        end
                    end
                    for i = (cl.pop ~= "" and 2 or 1), #c.stack do
                        ns[j] = c.stack[i]
                        j = j + 1
                    end
                    out[#out + 1] = {st = t.to, pos = c.pos + rd,
                                     stack = ns, steps = c.steps + 1}
                    eids[#eids + 1] = t.eid
                end
            end
        end
        return
    end
    for _, t in ipairs(m.tr[c.st] or {}) do
        if sym ~= nil and t.syms[sym] then
            out[#out + 1] = {st = t.to, pos = c.pos + 1}
            eids[#eids + 1] = t.eid
        end
        if t.eps then
            out[#out + 1] = {st = t.to, pos = c.pos}
            eids[#eids + 1] = t.eid
        end
    end
end

-- does this configuration accept right now?
local function accepts(m, run, c, n_succ)
    if m.tapes then
        return n_succ == 0 and m.acc[c.st] == true
    end
    if c.pos <= #run.toks then return false end
    if is_pda(m.type) then
        local acc = pda_accept(m.type)
        if acc == "f" then         -- L_F: state in F, stack arbitrary
            return m.acc[c.st] == true
        elseif acc == "e" then     -- L_E: stack empty, a NON-EMPTY
            return #c.stack == 0   -- computation (steps>0) so λ is
                   and c.steps > 0 -- not free
        end
        return #c.stack == 0 and m.acc[c.st] == true
    end
    return m.acc[c.st] == true
end

-- ---------- runs: three nondeterminism views -------------------------
--
--   set   breadth expansion: every live config advances per Step —
--         identical configs merge, already-seen ones are dropped
--   tree  JFLAP's clickable configuration tree: each config is a node;
--         clicking a leaf expands just that branch (Step expands the
--         whole frontier).  Configs repeating an ANCESTOR are loops
--         (marked, not expandable) — dedup is per-path, not global
--   pick  single path: the current config's options are listed and
--         the user clicks the move to take; only that branch lives

local nid = 0
local function mkconf(m, base, parent, eid)
    nid = nid + 1
    base.id, base.parent, base.eid = nid, parent, eid
    return base
end

local function conf0(m, toks)
    if m.tapes then
        local tp = {}
        for i, s in ipairs(toks) do tp[i] = s end
        local tapes, heads = {}, {}
        for i = 1, m.tapes do
            tapes[i] = (i == 1) and tp or {}
            heads[i] = 1
        end
        return {st = m.initial, tapes = tapes, heads = heads}
    elseif is_pda(m.type) then
        return {st = m.initial, pos = 1, stack = {}, steps = 0}
    end
    return {st = m.initial, pos = 1}
end

-- a config equal to one of its ancestors can only cycle — pruned
local function is_loop(m, c)
    local k = conf_key(m, c)
    local p = c.parent
    while p do
        if conf_key(m, p) == k then return true end
        p = p.parent
    end
    return false
end

-- a conf sits inside a folded subtree when any ancestor is folded —
-- hidden from the row list and not part of the visible frontier
local function under_fold(c)
    local p = c.parent
    while p do
        if p.fold then return true end
        p = p.parent
    end
    return false
end

-- canvas highlight per mode: live states are set's whole live set /
-- tree's open frontier / pick's current state.  The edge highlight
-- marks the transitions that could be taken NEXT (enabled successors
-- of the live confs — pick reuses its option list), so the student
-- sees the available moves before stepping; after a verdict nothing
-- stays green in set/pick, while tree keeps offering expandable
-- frontier moves
local function paint(run)
    local live, nxt = {}, {}
    if run then
        local m = run.m
        local confs
        if run.mode == "pick" then
            confs = run.cur and {run.cur} or {}
            if not run.verdict then
                for _, o in ipairs(run.opts or {}) do
                    if o.eid then nxt[o.eid] = true end
                end
            end
        else
            confs = {}
            if run.mode == "tree" then
                for _, c in ipairs(run.all) do
                    if c.fold then
                        -- folded boundary: visible, but its (hidden)
                        -- successors aren't offered as next moves
                        live[c.st] = true
                    elseif not c.kids and not c.loop and not c.done
                           and not under_fold(c) then
                        confs[#confs + 1] = c
                    end
                end
            else
                for _, c in ipairs(run.confs) do
                    confs[#confs + 1] = c
                end
            end
            if not run.verdict or run.mode == "tree" then
                for _, c in ipairs(confs) do
                    local out, eids = {}, {}
                    succs(m, run, c, out, eids)
                    for _, e in ipairs(eids) do nxt[e] = true end
                end
            end
        end
        for _, c in ipairs(confs) do live[c.st] = true end
        G.sim_edges = nxt
    else
        G.sim_edges = nil
    end
    G.sim_live = live
end

-- ---------- set mode --------------------------------------------------

local function set_step(run)
    local m = run.m
    local nxt, any_accept = {}, false
    for _, c in ipairs(run.confs) do
        local out, eids = {}, {}
        succs(m, run, c, out, eids)
        if accepts(m, run, c, #out) then any_accept = true end
        for i = 1, #out do
            local k = conf_key(m, out[i])
            if not run.seen[k] then
                run.seen[k] = true
                nxt[#nxt + 1] = mkconf(m, out[i], c, eids[i])
            end
        end
    end
    run.confs = nxt
    run.steps = run.steps + 1
    if any_accept then run.verdict = "accept"
    elseif #nxt == 0 then run.verdict = "reject"
    elseif run.steps >= MAX_STEPS then run.verdict = "step limit"
    elseif #nxt > MAX_CONFS then
        -- keep the live set bounded: drop the tail (breadth-first
        -- keeps the shallowest configs anyway)
        for i = #nxt, MAX_CONFS + 1, -1 do nxt[i] = nil end
        run.confs = nxt
        run.capped = true
    end
    paint(run)
end

-- ---------- tree mode -------------------------------------------------

local function tree_expand(run, c)
    if c.kids or c.loop or c.done then return end
    local m = run.m
    local out, eids = {}, {}
    succs(m, run, c, out, eids)
    c.kids = {}
    for i = 1, #out do
        local ch = mkconf(m, out[i], c, eids[i])
        -- finite/pda acceptance is decidable on arrival; tm's
        -- halt-in-accept is decidable only when expanded (below)
        if not m.tapes and accepts(m, run, ch, nil) then
            ch.done = true
        elseif is_loop(m, ch) then
            ch.loop = true
        end
        c.kids[#c.kids + 1] = ch
        run.all[#run.all + 1] = ch
    end
    if m.tapes and #out == 0 and m.acc[c.st] then c.done = true end
end

local function tree_verdict(run)
    local open = false
    for _, c in ipairs(run.all) do
        if c.done then return "accept" end
        if not c.kids and not c.loop then open = true end
    end
    return (not open) and "reject" or nil
end

local function tree_step(run)
    local leaves = {}
    for _, c in ipairs(run.all) do
        -- folded subtrees are frozen: their hidden leaves must not
        -- grow invisibly under the fold (unfolding would show
        -- content the student never saw computed)
        if not c.kids and not c.loop and not c.done
           and not under_fold(c) then
            leaves[#leaves + 1] = c
        end
    end
    for _, c in ipairs(leaves) do tree_expand(run, c) end
    run.steps = run.steps + 1
    run.verdict = tree_verdict(run)
    -- a reached verdict does NOT freeze the tree: accept stands, but
    -- the student may keep unfolding the remaining branches; only the
    -- growth caps stop expansion
    if run.steps >= MAX_STEPS or #run.all > 4 * MAX_CONFS then
        run.capped = true
        if not run.verdict then run.verdict = "step limit" end
    end
    paint(run)
end

-- clicking a leaf expands just that branch — stays available after an
-- accept verdict so the rest of the tree can still be explored.
-- clicking an expanded/folded node folds its subtree away or back —
-- display-only, the computed children stay
local function tree_click(run, c)
    if c.kids and #c.kids > 0 then
        c.fold = not c.fold and true or nil
        paint(run)
        return
    end
    if run.capped or run.verdict == "step limit" then return end
    tree_expand(run, c)
    run.verdict = tree_verdict(run)
    if #run.all > 4 * MAX_CONFS then
        run.capped = true
        if not run.verdict then run.verdict = "step limit" end
    end
    paint(run)
end

-- ---------- pick mode -------------------------------------------------

local function pick_refresh(run)
    local m, c = run.m, run.cur
    if not c then run.verdict = "reject" return end
    if accepts(m, run, c, nil) then
        c.done = true run.verdict = "accept" return
    end
    local out, eids = {}, {}
    succs(m, run, c, out, eids)
    if m.tapes and #out == 0 and m.acc[c.st] then
        c.done = true run.verdict = "accept" return
    end
    run.opts = {}
    for i = 1, #out do
        local ch = mkconf(m, out[i], c, eids[i])
        if is_loop(m, ch) then ch.loop = true end
        run.opts[#run.opts + 1] = ch
    end
    if #run.opts == 0 then
        run.verdict = "reject"
    elseif #run.trail >= MAX_STEPS then
        run.verdict = "step limit"
    end
end

local function pick_choose(run, ch)
    if run.verdict then return end
    run.cur = ch
    run.trail[#run.trail + 1] = ch
    run.opts = nil
    run.steps = run.steps + 1
    pick_refresh(run)
    paint(run)
end

-- ---------- word generation ------------------------------------------
--
-- same BFS the grader's automata.make_word_generator runs: every conf
-- carries the word produced so far, each step extends it by a usable
-- symbol, and accepting confs yield their word.  Breadth-first order =
-- shortest words first.  (The grader registers generation only for
-- finite and pushdown automata — no TM entry.)

local GEN_WORDS = 8        -- rows shown
local GEN_CAP = 40000    -- explored confs safety bound

local function gen_key(m, c)
    if is_pda(m.type) then
        return tostring(c.st) .. "@" .. c.word .. "|"
            .. table.concat(c.stack)
    end
    return tostring(c.st) .. "@" .. c.word
end

-- generation successors: a clause's own symbol extends the produced
-- word (λ clauses keep it); stack handling identical to the runs
local function gen_succs(m, c, out)
    if is_pda(m.type) then
        for _, t in ipairs(m.tr[c.st] or {}) do
            for _, cl in ipairs(t.cs) do
                if cl.pop == "" or c.stack[1] == cl.pop then
                    local ns, j = {}, 1
                    for i = 1, #cl.push do
                        ns[j] = cl.push:sub(i, i)
                        j = j + 1
                    end
                    for i = (cl.pop ~= "" and 2 or 1), #c.stack do
                        ns[j] = c.stack[i]
                        j = j + 1
                    end
                    out[#out + 1] = {st = t.to,
                                     word = c.word .. cl.input,
                                     stack = ns, steps = c.steps + 1}
                end
            end
        end
        return
    end
    for _, t in ipairs(m.tr[c.st] or {}) do
        for _, s in ipairs(t.sl) do
            out[#out + 1] = {st = t.to, word = c.word .. s}
        end
        if t.eps then
            out[#out + 1] = {st = t.to, word = c.word}
        end
    end
end

local function gen_accepts(m, c)
    if is_pda(m.type) then
        local acc = pda_accept(m.type)
        if acc == "f" then return m.acc[c.st] == true end
        if acc == "e" then return #c.stack == 0 and c.steps > 0 end
        return #c.stack == 0 and m.acc[c.st] == true
    end
    return m.acc[c.st] == true
end

local function gen_words(m, limit, cap)
    if m.tapes then return {}, "n/a", true end
    if not m.initial then return {}, "no initial state", true end
    limit = limit or GEN_WORDS
    cap = cap or GEN_CAP
    local words, q, seen, emitted, explored = {}, {}, {}, {}, 0
    local c0 = {st = m.initial, word = "",
                stack = is_pda(m.type) and {} or nil,
                steps = is_pda(m.type) and 0 or nil}
    q[1] = c0
    seen[gen_key(m, c0)] = true
    local head = 1
    while head <= #q and #words < limit do
        local c = q[head]
        head = head + 1
        explored = explored + 1
        if explored > cap then
            return words, "stopped early \xc2\xb7 cap", false
        end
        -- several accepting configurations can carry the SAME word
        -- (ε-paths, extra stack-pops): emit each word once
        if gen_accepts(m, c) and not emitted[c.word] then
            emitted[c.word] = true
            words[#words + 1] = c.word
        end
        local out = {}
        gen_succs(m, c, out)
        for _, s in ipairs(out) do
            local k = gen_key(m, s)
            if not seen[k] then
                seen[k] = true
                q[#q + 1] = s
            end
        end
    end
    -- third return: BFS drained the queue — the list is complete
    return words, nil, head > #q
end

-- ---------- shared -----------------------------------------------------

local function new_run(word, mode)
    local m = build()
    local toks = tokenize(word)
    local run = {m = m, toks = toks, steps = 0, verdict = nil,
                 ver = G.nodes_ver, mode = mode or G.sim_mode or "set"}
    if not m.initial then
        run.verdict = "reject"
        run.confs, run.all = {}, {}
        return run
    end
    local c0 = mkconf(m, conf0(m, toks))
    if run.mode == "tree" then
        run.all = {c0}
        if not m.tapes and accepts(m, run, c0, nil) then c0.done = true end
        run.verdict = tree_verdict(run)
        paint(run)
    elseif run.mode == "pick" then
        run.cur, run.trail = c0, {c0}
        pick_refresh(run)
        paint(run)
    else
        run.mode = "set"
        run.confs = {c0}
        run.seen = {[conf_key(m, c0)] = true}
        if accepts(m, run, c0, 1) then
            run.verdict = "accept"
        end
    end
    paint(run)
    return run
end

local function step(run)
    -- tree mode may keep unfolding past an accept verdict
    if run.verdict and not (run.mode == "tree"
                            and run.verdict == "accept"
                            and not run.capped) then return end
    if run.mode == "tree" then tree_step(run)
    elseif run.mode == "pick" then
        -- Step without a click choice takes the first live option
        if run.opts then
            local ch = run.opts[1]
            for _, o in ipairs(run.opts) do
                if not o.loop then ch = o break end
            end
            if ch then pick_choose(run, ch) end
        end
    else set_step(run) end
end

-- run to a verdict (or the caps)
local function run_all(run)
    if run.mode == "pick" then
        while not run.verdict and run.opts and #run.opts > 0 do
            step(run)
        end
    else
        while not run.verdict do step(run) end
    end
    paint(run)
    return run.verdict
end

-- headless verdict for the multi-run table — always the breadth mode,
-- independent of the section's display mode
local function evaluate(word)
    return run_all(new_run(word, "set"))
end

-- ---------- configuration display ----------------------------------

local function conf_text(m, run, c)
    local nm = m.names[c.st] or "?"
    if m.tapes then
        local parts = {nm}
        for i = 1, m.tapes do
            local h = c.heads[i]
            local cells = {}
            for d = -3, 3 do
                local s = c.tapes[i][h + d] or "\xe2\x8a\x94"
                cells[#cells + 1] = (d == 0) and ("[" .. s .. "]") or s
            end
            parts[#parts + 1] = table.concat(cells, " ")
        end
        return "(" .. table.concat(parts, " | ") .. ")"
    end
    local rest = {}
    for i = c.pos, #run.toks do rest[#rest + 1] = run.toks[i] end
    local w = #rest > 0 and table.concat(rest) or "\xce\xbb"
    if is_pda(m.type) then
        local st = #c.stack > 0 and table.concat(c.stack) or "\xce\xbb"
        return string.format("(%s, %s, %s)", nm, w, st)
    end
    return string.format("(%s, %s)", nm, w)
end

-- ---------- panel section ------------------------------------------

local word_buf = ffi.new("char[256]")
local word_init = false
local multi = {}
for i = 1, 4 do
    multi[i] = {buf = ffi.new("char[128]"), res = nil}
end

local function reset()
    G.sim = nil
    paint(nil)
end

-- disclosure marker, styled on nk_tree (NK_TREE_NODE): a vector
-- triangle in its own leading column — ▼ expanded, ▶ collapsed with
-- content, ▶-outline for an expandable leaf (nothing computed inside
-- yet).  Vector-drawn like Nuklear's nk_do_button_symbol — the UI
-- font subset has no triangle glyphs.  marker="none" keeps the column
-- so sibling rows stay text-aligned
local MARK_W = 15
local function draw_marker(bx, by, bh, marker)
    local buf = A.canvas()
    local s = 5
    local cx, cy = bx + 7, by + bh * 0.5
    local r, g, b, a = util.col(TH.GREY_DARK)
    if marker == "open" then
        A.fill_triangle(buf, cx - s, cy - s * 0.6, cx + s, cy - s * 0.6,
                        cx, cy + s, r, g, b, a)
    elseif marker == "fold" then
        A.fill_triangle(buf, cx - s * 0.6, cy - s,
                        cx - s * 0.6, cy + s, cx + s, cy, r, g, b, a)
    elseif marker == "leaf" then
        A.stroke_line(buf, cx - s * 0.6, cy - s, cx + s, cy,
                      1.0, r, g, b, a)
        A.stroke_line(buf, cx + s, cy, cx - s * 0.6, cy + s,
                      1.0, r, g, b, a)
        A.stroke_line(buf, cx - s * 0.6, cy + s, cx - s * 0.6, cy - s,
                      1.0, r, g, b, a)
    end
end

-- a config row: nk_selectable_label when the row takes a click (tree
-- leaves, pick options — stock hover highlight + hand cursor), plain
-- nk_label otherwise.  indent is a static spacer column so the
-- selectable keeps claiming the row's whole remainder; marker adds a
-- second static column for the disclosure triangle
local function conf_row(text, indent, color, clickable, marker)
    local fh = A.font_height()
    local pad = indent or 0
    if marker then
        A.content_rect(f4)
        local wide = f4[2]
        A.row_begin(1, fh + 4, 3)      -- fmt: non-zero = NK_STATIC
        A.row_push(math.max(1, pad))
        A.spacing(1)
        A.row_push(MARK_W)
        A.widget(f4)                   -- marker cell (allocates col 1)
        local mx, my, mh = f4[0], f4[1], f4[3]
        A.row_push(math.max(40, wide - pad - MARK_W))
        draw_marker(mx, my, mh, marker)
    elseif pad > 0 then
        A.content_rect(f4)
        A.row_begin(1, fh + 4, 2)
        A.row_push(pad)
        A.spacing(1)
        A.row_push(math.max(40, f4[2] - pad))
    else
        A.row(fh + 4, 1)
    end
    A.text_color(pk(color))
    local clicked = false
    if clickable then
        clicked = A.selectable(text, NK.TEXT_LEFT, 0) ~= 0
    else
        A.label(text, NK.TEXT_LEFT)
    end
    A.text_color(pk(TH.BLACK))
    if marker or pad > 0 then A.row_end() end
    return clicked
end

-- nondeterminism views (radio: exactly one on); only the types that
-- can branch offer them — DFA variants and Turing machines are
-- deterministic by construction, so there the selector is hidden
local MODES = {
    {"set",  "set \xc2\xb7 all branches live"},
    {"tree", "tree \xc2\xb7 click to expand"},
    {"pick", "pick \xc2\xb7 choose each move"},
}
-- the nondeterminism views make sense only where the type allows
-- branching: NFA variants, the nondeterministic PDA types and ntm*;
-- dfa*, dpda* and tm* are deterministic by definition
local NONDET_TYPE = {nfa = true, ["nfa-eps"] = true,
                     pda = true, ["pda-f"] = true, ["pda-e"] = true,
                     ntm = true}
local function is_nondet_type(t)
    return NONDET_TYPE[t or ""] == true
        or (t or ""):match("^ntm%-") ~= nil
end
local TREE_ROWS = 14

local function verdict_label(cur)
    A.row(20, 1)
    A.text_color(pk(cur.verdict == "accept" and C_GREEN
                    or cur.verdict == "reject" and C_RED or C_AMBER))
    A.label(cur.verdict == "accept" and "accepted"
            or cur.verdict == "reject" and "rejected"
            or cur.verdict, NK.TEXT_LEFT)
    A.text_color(pk(TH.BLACK))
end

-- depth-first flatten of the configuration tree for display
local function tree_flat(run, out)
    local function walk(c, d)
        out[#out + 1] = {c = c, d = d}
        if c.kids and not c.fold then
            for _, ch in ipairs(c.kids) do walk(ch, d + 1) end
        end
    end
    for _, c in ipairs(run.all) do if not c.parent then walk(c, 0) end end
    return out
end

local function ndesc(c)
    local n = 0
    for _, k in ipairs(c.kids or {}) do n = n + 1 + ndesc(k) end
    return n
end

-- row status of a tree node; the UI font has no check/loop glyphs,
-- so states read as coloured words instead
local function conf_row_kind(c)
    if c.done then return "accept", C_GREEN
    elseif c.loop then return "loop", C_AMBER
    elseif c.kids then
        if #c.kids == 0 then return "dead", C_HINT end
        if c.fold then return "fold", TH.BLACK end
        return "open", TH.BLACK
    end
    return "leaf", TH.BLACK
end

local SUFFIX = {accept = " \xc2\xb7 accepted", loop = " \xc2\xb7 loop",
                dead = " \xc2\xb7 stuck"}

local function sim_confs(cur)
    local m = cur.m
    if cur.mode == "tree" then
        local flat = tree_flat(cur, {})
        local shown = math.min(TREE_ROWS, #flat)
        for i = 1, shown do
            local c, d = flat[i].c, flat[i].d
            local kind, colr = conf_row_kind(c)
            local suf = SUFFIX[kind]
                        or (kind == "fold"
                            and string.format(" \xc2\xb7 %d more",
                                              ndesc(c)) or nil)
            -- fold/unfold is display-only: always clickable; expanding
            -- a leaf respects the growth caps
            local clickable = kind == "open" or kind == "fold"
                or (kind == "leaf" and not cur.capped
                    and cur.verdict ~= "step limit")
            local marker = (kind == "leaf" or kind == "open"
                            or kind == "fold") and kind or "none"
            if conf_row(conf_text(m, cur, c) .. (suf or ""),
                        math.min(d, 8) * 14, colr, clickable,
                        marker) then
                tree_click(cur, c)
            end
        end
        if #flat > shown then
            A.row(20, 1)
            A.label(string.format("… %d more", #flat - shown),
                    NK.TEXT_LEFT)
        end
        return
    end
    if cur.mode == "pick" then
        -- the path so far (last few configs), then the options
        local t0 = math.max(1, #cur.trail - 3)
        for i = t0, #cur.trail do
            local c = cur.trail[i]
            conf_row(conf_text(m, cur, c), 0,
                     i == #cur.trail and TH.BLACK or C_HINT, false)
        end
        if cur.opts and not cur.verdict then
            for _, o in ipairs(cur.opts) do
                local via = m.lbl[o.eid] or ""
                local txt = "\xc2\xbb " .. conf_text(m, cur, o)
                    .. "  \xc2\xb7 " .. (via ~= "" and via or "?")
                    .. (o.loop and " \xc2\xb7 loop" or "")
                if conf_row(txt, 14, o.loop and C_AMBER or TH.BLACK,
                            true) then
                    pick_choose(cur, o)
                end
            end
        end
        return
    end
    -- set: plain preview of the live set
    for i = 1, math.min(PREVIEW, #cur.confs) do
        conf_row(conf_text(m, cur, cur.confs[i]), 0, TH.BLACK, false)
    end
    if #cur.confs > PREVIEW then
        A.row(20, 1)
        A.label(string.format("… %d more", #cur.confs - PREVIEW),
                NK.TEXT_LEFT)
    end
    if cur.capped then
        A.row(20, 1); A.text_color(pk(C_AMBER))
        A.label("configuration cap \xc2\xb7 run may be incomplete",
                NK.TEXT_LEFT)
        A.text_color(pk(TH.BLACK))
    end
end

function sim.section(disc_row)
    if not G.sim_enabled or G.mode == "re" then return end
    -- the machine is re-read at run start; edits mid-run invalidate
    if G.sim and G.sim.ver ~= G.nodes_ver then
        reset()
        G.sim_note = "automaton changed \xc2\xb7 run reset"
    end
    local cur = G.sim
    local nlive = 0
    if cur then
        if cur.mode == "tree" then nlive = #cur.all
        elseif cur.mode == "pick" then nlive = #cur.trail
        else nlive = #cur.confs end
    end
    local title = "Simulate"
    if cur and cur.verdict then
        title = title .. " \xc2\xb7 " .. cur.verdict
    elseif cur then
        title = title .. string.format(" \xc2\xb7 step %d, %d live",
                                       cur.steps, nlive)
    end
    if disc_row(title, G.sim_open) then
        G.sim_open = not G.sim_open
    end
    if not G.sim_open then return end

    -- view selector: one of the three nondeterminism views; switching
    -- drops the current run (same word can simply be re-run).  Only
    -- shown for types that can branch — a deterministic automaton has
    -- one live configuration anyway, so the choice is hidden there.
    G.sim_mode = G.sim_mode or "set"
    if is_nondet_type(G.aut_type or "nfa") then
        for _, md in ipairs(MODES) do
            A.row(20, 1)
            if A.option(md[2], G.sim_mode == md[1] and 1 or 0) ~= 0 then
                if G.sim_mode ~= md[1] then
                    G.sim_mode = md[1]
                    reset()
                end
            end
        end
    elseif G.sim_mode ~= "set" then
        G.sim_mode = "set"
        reset()
    end

    A.row(20, 1); A.label("Input word", NK.TEXT_LEFT)
    A.row(26, 1)
    if not word_init then word_init = true set_str(word_buf, "") end
    local ev = A.edit_zt(NK.EDIT_FIELD
                         | (G.readonly and NK.EDIT_READ_ONLY or 0),
                         word_buf, 255)
    if util.hasflag(ev, NK.EDIT_ACTIVE) then G.edit_seen = true end

    -- Start materialises the initial configuration (state highlighted,
    -- config row shown) and only then turns into Step — otherwise the
    -- first button press jumps a whole move without ever showing what
    -- the machine started in
    A.row(24, 3)
    if A.button(cur and "Step" or "Start") ~= 0 then
        if not cur then
            cur = new_run(ffi.string(word_buf))
            G.sim = cur
        else
            step(cur)
        end
        G.sim_note = nil
        cur = G.sim
    end
    if A.button("Run") ~= 0 then
        if not cur then cur = new_run(ffi.string(word_buf)) G.sim = cur end
        G.sim_note = nil
        run_all(cur)
    end
    if A.button("Clear") ~= 0 then
        reset() cur = nil G.sim_note = nil
    end

    cur = G.sim
    if G.sim_note then
        A.row(20, 1)
        A.text_color(pk(C_AMBER))
        A.label(G.sim_note, NK.TEXT_LEFT)
        A.text_color(pk(TH.BLACK))
    end
    if cur and #cur.m.errs > 0 then
        A.text_color(pk(C_AMBER))
        for i = 1, math.min(3, #cur.m.errs) do
            A.row(20, 1)
            A.label("label: " .. cur.m.errs[i], NK.TEXT_LEFT)
        end
        A.text_color(pk(TH.BLACK))
    end
    if not cur then
        A.row(20, 1)
        A.text_color(pk(C_HINT))
        A.label("Start shows the initial config,", NK.TEXT_LEFT)
        A.row(20, 1)
        A.label("Step walks one round of moves", NK.TEXT_LEFT)
        A.text_color(pk(TH.BLACK))
    else
        if not cur.m.initial then
            A.row(20, 1); A.text_color(pk(C_RED))
            A.label("no initial state", NK.TEXT_LEFT)
            A.text_color(pk(TH.BLACK))
        end
        sim_confs(cur)
        if cur.verdict then verdict_label(cur) end
    end

    -- multi-run: a small word table evaluated headlessly, JFLAP's
    -- "Multiple Run" — same machine build, no canvas state
    if disc_row("Multi-run", G.sim_multi_open) then
        G.sim_multi_open = not G.sim_multi_open
    end
    if G.sim_multi_open then
        for i = 1, #multi do
            local r = multi[i]
            A.row(24, 3)
            local mev = A.edit_zt(NK.EDIT_FIELD
                | (G.readonly and NK.EDIT_READ_ONLY or 0), r.buf, 127)
            if util.hasflag(mev, NK.EDIT_ACTIVE) then
                G.edit_seen = true
            end
            if A.button("Run") ~= 0 then
                r.res = evaluate(ffi.string(r.buf))
            end
            local res = r.res or "-"
            A.text_color(pk(res == "accept" and C_GREEN
                            or res == "reject" and C_RED
                            or res == "-" and TH.BLACK or C_AMBER))
            A.label(res, NK.TEXT_LEFT)
            A.text_color(pk(TH.BLACK))
        end
    end

    -- accepted words, shortest first (BFS — same enumeration the
    -- grader's word generator does).  Clicking a word loads it into
    -- the input field and starts a run, so the trace itself is the
    -- visualisation.  Not offered for TMs (no generation entry in
    -- the grader's acceptance_map either).
    local tapes = (ll and ll.tapes(G.aut_type or ""))
                  or ((G.aut_type == "tm" or G.aut_type == "ntm")
                      and 1 or nil)
    if not tapes then
        if disc_row("Accepted words", G.gen_open) then
            G.gen_open = not G.gen_open
        end
        if G.gen_open then
            if not G.gen or G.gen.ver ~= G.nodes_ver then
                G.gen_limit = GEN_WORDS     -- fresh automaton: page one
            end
            local want = G.gen_limit
            if not G.gen or G.gen.ver ~= G.nodes_ver
               or G.gen.limit ~= want then
                -- deeper pages also get a proportionally deeper
                -- exploration budget (re-run is cheap + deterministic)
                local w, note, done = gen_words(
                    build(), want, GEN_CAP * math.ceil(want / GEN_WORDS))
                G.gen = {ver = G.nodes_ver, words = w, note = note,
                         limit = want, done = done}
            end
            local g = G.gen
            -- BFS still had confs queued: offer another page.  The
            -- row sits ABOVE the list so it is visible without
            -- scrolling when the section opens (and again at the
            -- bottom once the list has grown past a page)
            local function more_row()
                return conf_row("\xc2\xbb more", 8, C_HINT, true)
            end
            if not g.done and #g.words > 0 and more_row() then
                G.gen_limit = g.limit + GEN_WORDS
            end
            for _, w in ipairs(g.words) do
                if conf_row("\xc2\xbb "
                            .. (w ~= "" and w or "\xce\xbb"),
                            8, TH.BLACK, true) then
                    set_str(word_buf, w)
                    G.sim = new_run(w)
                    G.sim_note = nil
                end
            end
            if #g.words == 0 then
                A.row(20, 1)
                A.text_color(pk(g.done and C_HINT or C_AMBER))
                A.label(g.note or "no accepted words found",
                        NK.TEXT_LEFT)
                A.text_color(pk(TH.BLACK))
            elseif g.done then
                A.row(20, 1)
                A.text_color(pk(C_HINT))
                A.label("\xc2\xb7 all accepted words", NK.TEXT_LEFT)
                A.text_color(pk(TH.BLACK))
            elseif g.note then
                A.row(20, 1)
                A.text_color(pk(C_AMBER))
                A.label(g.note, NK.TEXT_LEFT)
                A.text_color(pk(TH.BLACK))
            end
            if not g.done
               and (#g.words == 0 or #g.words > GEN_WORDS)
               and more_row() then
                G.gen_limit = g.limit + GEN_WORDS
            end
        end
    end
end

-- AUT_SIM="word;steps;mode" (dev): open the section, seed the word
-- and step a few times so screenshots show live highlighting; mode is
-- one of set|tree|pick (default set)
function sim.dev_run(spec)
    local w, n, md = tostring(spec or "")
        :match("^([^;]*);?(%d*);?(%a*)$")
    G.sim_open = true
    G.gen_open = os.getenv and os.getenv("AUT_GEN") == "1"
    G.sim_mode = (md == "tree" or md == "pick") and md or "set"
    set_str(word_buf, w or "")
    local r = new_run(w or "")
    G.sim = r
    paint(r)
    for _ = 1, tonumber(n) or 1 do
        if r.verdict then break end
        step(r)
    end
end

-- test hooks (headless): no A.* touched above the panel section
sim._build    = build
sim._new_run  = new_run
sim._step     = step
sim._run_all  = run_all
sim._evaluate = evaluate
sim._reset    = reset
sim._tokenize = tokenize
sim._tree_click  = tree_click
sim._tree_flat   = tree_flat
sim._pick_choose = pick_choose
sim._gen      = gen_words

return sim
