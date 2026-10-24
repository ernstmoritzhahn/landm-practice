-- wordproof/regexp_check.lua — grading for "give a regular expression"
-- tasks (exercise 1.2): parse the student's regexp leniently, determinise
-- it and compare its language against the task's reference DFA via the
-- product construction (automata.compare_dfa gives witness words for the
-- difference).
--
-- M.check(task, expr_str) -> res table for the GUI:
--   {ok=true}                          language equivalent
--   {ok=false, kind=..., msg=...}      parse error / not equivalent /
--                                      undecidable within the state cap

require("lib.util").fix_path()
local automata = require "automata"

local M = {}

local MAX_STATES = 500    -- subset-construction cap for student input

local function word_or_lam(w)
    if w == nil then return nil end
    if w == "" then return "λ" end
    return w
end

local function to_dfa(re)
    local nfa = automata.regexp_to_nfa_lambda(re)
    return automata.nfa_to_dfa(nfa, MAX_STATES)
end

-- compile the task's reference expression once per task/table lifetime
local function reference_dfa(task)
    if task._ref_dfa then return task._ref_dfa end
    local re = automata.parse_regexp_string(task.reference)
    local dfa = to_dfa(re)
    assert(dfa, "reference regexp too large: " .. tostring(task.reference))
    task._ref_dfa = dfa
    return dfa
end

function M.check(task, expr_str)
    expr_str = expr_str or ""
    if not expr_str:match("%S") then
        return { ok=false, kind="empty",
                 msg="enter a regular expression" }
    end
    local ok, re = pcall(automata.parse_regexp_string_lenient, expr_str)
    if not ok then
        return { ok=false, kind="parse",
                 msg=tostring(re):gsub("^[^:]+:%d+: *", "") }
    end
    local ok2, student = pcall(to_dfa, re)
    if not ok2 or not student then
        return { ok=false, kind="too_large",
                 msg="your expression builds an automaton too large to "
                  .. "verify (>" .. MAX_STATES .. " states)" }
    end
    local cmp, cex_s, cex_r =
        automata.compare_dfa(student, reference_dfa(task))
    if cmp == "=" then
        return { ok=true }
    end
    local parts = {}
    if cex_s then
        parts[#parts+1] = "'" .. word_or_lam(cex_s)
            .. "' is matched but not in L"
    end
    if cex_r then
        parts[#parts+1] = "'" .. word_or_lam(cex_r)
            .. "' is in L but not matched"
    end
    return { ok=false, kind="mismatch",
             msg=table.concat(parts, ";  ") }
end

return M
