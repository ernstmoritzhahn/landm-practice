-- logic/ — shared formal-logic backend (Advanced Logic course).
--
-- Phase-0 facade: parsing, AST utilities, unification, evaluation.
-- Used by the formula-input demonstrator now and by the wordproof-style
-- checkers (truth tables, BDD, tableaux, Gentzen, CNF/resolution, MGU)
-- next — same code path in the wasm worker and the grading container.

local logic = {}

logic.operators  = require "logic.operators"
logic.syntax     = require "logic.syntax"
logic.formula    = require "logic.formula"
logic.unify      = require "logic.unify"
logic.eval       = require "logic.eval"
logic.tree_layout = require "logic.tree_layout"

logic.parse       = logic.syntax.parse
logic.parse_term  = logic.syntax.parse_term
logic.suggest     = logic.syntax.suggest
logic.highlight   = logic.syntax.highlight
logic.render      = logic.formula.render
logic.render_term = logic.formula.render_term
logic.free_vars   = logic.formula.free_vars
logic.atoms       = logic.formula.atoms
logic.closed      = logic.formula.closed
logic.equal       = logic.formula.equal
logic.subst_formula = logic.formula.subst_formula
logic.subst_term  = logic.formula.subst_term
logic.mgu         = logic.unify.mgu
logic.mgu_atoms   = logic.unify.mgu_atoms
logic.unify_pairs = logic.unify.unify_pairs
logic.compose     = logic.unify.compose
logic.render_subst = logic.unify.render_subst
logic.eval_prop   = logic.eval.eval_prop
logic.evaluate    = logic.eval.eval
logic.layout      = logic.tree_layout.layout

return logic
