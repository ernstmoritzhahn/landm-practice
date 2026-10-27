-- wordproof/re_steps.lua — generate the stepwise RE -> NFA-λ part
-- lists (free-form and guided variants) from a regular expression.
--
-- The step chain mirrors the lecture's Thompson construction: every
-- literal atom gets a base step (deduplicated, sorted), then every
-- composite sub-expression gets a step in postorder — concat/choice
-- steps compose their operand steps, star/plus steps wrap one.  A
-- sub-expression occurring several times produces ONE step; later
-- occurrences reuse it as a component (a concat of a stage with
-- itself embeds two copies).
--
-- Free variant: each part lists the earlier part indices whose
-- automata can be inserted (`seeds`).  Guided variant: each composite
-- step embeds its operand stages as locked components
-- (`seeds_locked`, repeats tagged "#2", …) and is followed by an
-- optional simplify slot — except a multi-operand step whose operands
-- are all the same stage (bb/aa embed two copies of one component:
-- no simplify slot there, matching the hand-written tasks).
--
-- Stage ids ("sid") are mnemonics derived from the sub-expression:
-- atom -> literal, concat -> sids joined, star -> sid.."S",
-- plus -> sid.."P", root union -> "u", inner union -> longest common
-- operand-prefix merge ("ba|bb" -> "bab"); collisions get "_2"…
-- Keeping these stable matters: saved student canvases tag embedded
-- component nodes with them.

local M = {}

-- automata is a directory module (automata/init.lua): fix_path adds
-- ./?/init.lua so `require "automata"` resolves no matter which
-- module loaded first (tasks.lua calls M.parts at definition time)
require("lib.util").fix_path()

local ATOM = { regexp_primitive = true, regexp_blank = true,
               regexp_empty = true }

local function canon(n)
    return tostring(n)                    -- ∪-joined canonical form
end

local function ref_of(n)
    return (canon(n):gsub("∪", "|"))
end

local function disp_of(n)
    return (canon(n):gsub("∪", " ∪ "))
end

-- ordered step list: atoms first (sorted), then composites in
-- postorder — both deduplicated by canonical form
local function collect(ast)
    local atoms, comps = {}, {}
    local seen = {}
    local function walk(n)
        local ty = n:get_type()
        if ATOM[ty] then
            local c = canon(n)
            if not seen[c] then
                seen[c] = true
                atoms[#atoms + 1] = n
            end
            return
        end
        if ty == "regexp_sequence" or ty == "regexp_choice" then
            walk(n:get_left())
            walk(n:get_right())
        else   -- regexp_repetition / regexp_plus
            walk(n:get_inner())
        end
        local c = canon(n)
        if not seen[c] then
            seen[c] = true
            comps[#comps + 1] = n
        end
    end
    walk(ast)
    table.sort(atoms, function(p, q) return canon(p) < canon(q) end)
    return atoms, comps
end

-- operands of a composite as a node list (duplicates kept — they
-- drive the "#2" copy tags)
local function operands(n)
    local ty = n:get_type()
    if ty == "regexp_sequence" or ty == "regexp_choice" then
        return { n:get_left(), n:get_right() }
    elseif ty == "regexp_repetition" or ty == "regexp_plus" then
        return { n:get_inner() }
    end
    return {}
end

local function lcp(a, b)
    local i = 1
    while i <= #a and i <= #b and a:sub(i, i) == b:sub(i, i) do
        i = i + 1
    end
    return i - 1
end

local function sid_of(n, is_root, used)
    local ty = n:get_type()
    local sid
    if ty == "regexp_primitive" then
        sid = n:get_inner()
    elseif ty == "regexp_blank" then
        sid = "λ"
    elseif ty == "regexp_empty" then
        sid = "∅"
    elseif ty == "regexp_sequence" then
        sid = n._sid_l .. n._sid_r
    elseif ty == "regexp_repetition" then
        sid = n._sid_l .. "S"
    elseif ty == "regexp_plus" then
        sid = n._sid_l .. "P"
    else   -- regexp_choice
        if is_root then
            sid = "u"
        else
            local a, b = n._sid_l, n._sid_r
            local p = lcp(a, b)
            if p > 0 then
                sid = a:sub(1, p) .. a:sub(p + 1) .. b:sub(p + 1)
            else
                sid = a .. "u" .. b
            end
        end
    end
    local base, k = sid, 2
    while used[sid] do
        sid = base .. "_" .. k
        k = k + 1
    end
    return sid
end

-- assign sids to every unique step node; children first (postorder
-- is exactly the comps/atoms order, so operand sids are already in
-- the canon-keyed map when a composite is marked — including
-- deduplicated repeat operands like the second x in x·x, whose node
-- object itself never gets marked).  Returns the map canon -> sid.
local function assign_sids(ast, atoms, comps)
    local used, sid = {}, {}
    local function mark(n, is_root)
        local ops = operands(n)
        n._sid_l = ops[1] and sid[canon(ops[1])]
        n._sid_r = ops[2] and sid[canon(ops[2])]
        local s = sid_of(n, is_root, used)
        used[s] = true
        sid[canon(n)] = s
        n._sid = s
    end
    for _, n in ipairs(atoms) do mark(n) end
    for _, n in ipairs(comps) do mark(n, n == ast) end
    return sid
end

-- free-variant part row
local function free_step(disp, ref, seeds, alphabet)
    return { kind = "aut", aut_type = "nfa-eps",
             alphabet = alphabet, label = disp,
             reference = ref, seeds = seeds }
end

local function gstep(sid, label, reference, seeds, alphabet)
    return { kind = "aut", aut_type = "nfa-eps",
             alphabet = alphabet,
             label = label, reference = reference,
             sub = sid .. ")", sid = sid, seeds_locked = seeds,
             check = "compose" }
end

local function sstep(sid, reference, alphabet)
    return { kind = "aut", aut_type = "nfa-eps",
             alphabet = alphabet,
             label = "optional: simplify — 'take over' adopts the "
                .. "automaton above; simplify it by hand",
             sub = sid .. "')",
             takeover_from = sid, reference = reference,
             optional = true }
end

-- label phrases ----------------------------------------------------
local function free_label(n)
    local ty = n:get_type()
    if ATOM[ty] then
        return "E = " .. disp_of(n)
    end
    local ops = operands(n)
    local d = "E = " .. disp_of(n)
    if ty == "regexp_repetition" or ty == "regexp_plus" then
        return d .. " — from the NFA for " .. disp_of(ops[1])
    end
    if canon(ops[1]) == canon(ops[2]) then
        return d .. " — from the NFA for " .. disp_of(ops[1])
               .. " (insert twice)"
    end
    return d .. " — from the NFAs for " .. disp_of(ops[1])
           .. " and " .. disp_of(ops[2])
end

local function guided_label(n, is_root)
    local ty = n:get_type()
    if ATOM[ty] then
        return "E = " .. disp_of(n)
    end
    local ops = operands(n)
    local distinct, seen = 0, {}
    for _, o in ipairs(ops) do
        if not seen[canon(o)] then
            seen[canon(o)] = true
            distinct = distinct + 1
        end
    end
    local what
    if distinct <= 1 then
        if #ops > 1 then
            what = "on the given component (embedded "
                   .. (#ops == 2 and "twice" or #ops .. " times")
                   .. ")"
        else
            what = "on the given component"
        end
    elseif is_root and distinct == 2 then
        what = "the two components"
    else
        what = "the given components"
    end
    return "E = " .. disp_of(n) .. " — compose " .. what
end

-- ------------------------------------------------------------------
-- M.parts(re_str, opts) -> free_parts, guided_parts
--   opts.alphabet    part alphabet (default "a,b")
--   opts.first_hint  appended in parens to the FREE variant's first
--                    composite label (tutorial hint on the sheet's
--                    first construction)
-- Errors on an unparseable expression (task definitions are authored
-- data — a bad regex should fail the build, not degrade silently).
function M.parts(re_str, opts)
    opts = opts or {}
    local alphabet = opts.alphabet or "a,b"
    local automata = require "automata"
    local ast = automata.parse_regexp_string(re_str)
    assert(ast, "re_steps: cannot parse '" .. re_str .. "'")
    local atoms, comps = collect(ast)
    local sid = assign_sids(ast, atoms, comps)
    local idx = {}                     -- canon -> free-part index
    local steps = {}                   -- ordered unique step nodes
    for _, n in ipairs(atoms) do
        idx[canon(n)] = #steps + 1
        steps[#steps + 1] = n
    end
    for _, n in ipairs(comps) do
        idx[canon(n)] = #steps + 1
        steps[#steps + 1] = n
    end

    local free, guided = {}, {}
    local first_composite = true
    for _, n in ipairs(steps) do
        local ty = n:get_type()
        if ATOM[ty] then
            free[#free + 1] =
                free_step("E = " .. disp_of(n), ref_of(n), nil,
                          alphabet)
            guided[#guided + 1] =
                gstep(n._sid, "E = " .. disp_of(n), ref_of(n), nil,
                      alphabet)
        else
            -- seeds: operand part indices, operand order, deduplicated
            local seeds, seen = {}, {}
            for _, o in ipairs(operands(n)) do
                local k = idx[canon(o)]
                if not seen[k] then
                    seen[k] = true
                    seeds[#seeds + 1] = k
                end
            end
            local label = free_label(n)
            if first_composite and opts.first_hint then
                label = label .. " (" .. opts.first_hint .. ")"
            end
            first_composite = false
            free[#free + 1] =
                free_step(label, ref_of(n), seeds, alphabet)

            -- seeds_locked: operand stage tags, repeats as "#k"
            local locked, count = {}, {}
            for _, o in ipairs(operands(n)) do
                local s = sid[canon(o)]
                count[s] = (count[s] or 0) + 1
                locked[#locked + 1] =
                    count[s] > 1 and s .. "#" .. count[s] or s
            end
            guided[#guided + 1] =
                gstep(n._sid, guided_label(n, n == ast), ref_of(n),
                      locked, alphabet)
            -- no simplify slot when a step composes several copies
            -- of ONE stage (bb/aa in the hand-written tasks)
            if not (#seeds == 1 and #locked > 1) then
                guided[#guided + 1] =
                    sstep(n._sid, ref_of(n), alphabet)
            end
        end
    end
    return free, guided
end

-- display form of a regex for task titles ("(ab)* ∪ a*")
function M.display(re_str)
    local automata = require "automata"
    local ast = automata.parse_regexp_string(re_str)
    assert(ast, "re_steps: cannot parse '" .. re_str .. "'")
    return disp_of(ast)
end

return M
