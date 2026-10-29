-- Operator table for classical logic (propositional + predicate),
-- Advanced Logic course / Ben-Ari notation.
--
-- Same field shape as bayesian_networks/logic/operators.lua
-- (is_operator/name/symbols/default_symbol/arity/precedence/notation/
-- associativity/associative) so the tables stay interchangeable where a
-- shared engine is wanted.  `key` names the AST op; `latex` is for
-- rendering.  Word aliases ("and", "forall", ...) are matched with
-- identifier boundaries by the parser, so they never clash with
-- ordinary symbol names.

local operators = {}

-- infix symbol lists must be longest-first inside each entry
-- (string_array_S tries array order).
operators.connectives = {
    {
        is_operator = true,
        name = "not",
        key = "not",
        symbols = {"¬", "~", "!"},
        word_symbols = {"not", "\\neg", "\\lnot"},
        default_symbol = "¬",
        latex = "\\neg",
        arity = 1,
        precedence = 5,
        notation = "prefix",
    },
    {
        is_operator = true,
        name = "and",
        key = "and",
        symbols = {"∧", "&&", "&", "/\\", "^"},
        word_symbols = {"and", "\\land", "\\wedge"},
        default_symbol = "∧",
        latex = "\\wedge",
        arity = 2,
        precedence = 4,
        notation = "infix",
        associativity = "right",
        associative = true,
    },
    {
        is_operator = true,
        name = "nand",
        key = "nand",
        symbols = {"↑"},
        word_symbols = {"nand", "\\uparrow", "\\up", "\\nand"},
        default_symbol = "↑",
        latex = "\\uparrow",
        arity = 2,
        precedence = 4,
        notation = "infix",
        associativity = "right",
    },
    {
        is_operator = true,
        name = "or",
        key = "or",
        symbols = {"∨", "||", "|", "\\/"},
        word_symbols = {"or", "\\lor", "\\vee"},
        default_symbol = "∨",
        latex = "\\vee",
        arity = 2,
        precedence = 3,
        notation = "infix",
        associativity = "right",
        associative = true,
    },
    {
        is_operator = true,
        name = "nor",
        key = "nor",
        symbols = {"↓"},
        word_symbols = {"nor", "\\downarrow", "\\down", "\\nor"},
        default_symbol = "↓",
        latex = "\\downarrow",
        arity = 2,
        precedence = 3,
        notation = "infix",
        associativity = "right",
    },
    {
        is_operator = true,
        name = "implication",
        key = "imp",
        symbols = {"→", "->", "=>"},
        word_symbols = {"implies", "\\to", "\\rightarrow", "\\ra", "\\implies"},
        default_symbol = "→",
        latex = "\\rightarrow",
        arity = 2,
        precedence = 2,
        notation = "infix",
        associativity = "right",
    },
    {
        is_operator = true,
        name = "revimplication",
        key = "revimp",
        symbols = {"←", "<-", "<="},
        word_symbols = {"\\leftarrow", "\\la", "\\gets"},
        default_symbol = "←",
        latex = "\\leftarrow",
        arity = 2,
        precedence = 2,
        notation = "infix",
        associativity = "right",
    },
    {
        is_operator = true,
        name = "biimplication",
        key = "iff",
        symbols = {"↔", "<->", "<=>", "=="},
        word_symbols = {"iff", "\\leftrightarrow", "\\Leftrightarrow", "\\lra", "\\iff"},
        default_symbol = "↔",
        latex = "\\leftrightarrow",
        arity = 2,
        precedence = 1,
        notation = "infix",
        associativity = "right",
    },
    {
        is_operator = true,
        name = "xor",
        key = "xor",
        symbols = {"⊕", "≢"},
        word_symbols = {"xor", "\\oplus", "\\xor"},
        default_symbol = "⊕",
        latex = "\\oplus",
        arity = 2,
        precedence = 1,
        notation = "infix",
        associativity = "right",
    },
}

operators.quantifiers = {
    {
        name = "forall",
        symbols = {"∀"},
        word_symbols = {"forall", "all", "\\forall"},
        default_symbol = "∀",
        latex = "\\forall",
    },
    {
        name = "exists",
        symbols = {"∃"},
        word_symbols = {"exists", "some", "\\exists"},
        default_symbol = "∃",
        latex = "\\exists",
    },
}

-- Boolean constants: `symbols` matched verbatim, `word_symbols` need
-- identifier boundaries.  Bare T/F stay identifiers (they are legit
-- atom/term names in predicate logic).
operators.constants = {
    {name = "true", symbols = {"⊤"}, word_symbols = {"true", "\\top"},
     default_symbol = "⊤", latex = "\\top"},
    {name = "false", symbols = {"⊥"}, word_symbols = {"false", "\\bot"},
     default_symbol = "⊥", latex = "\\bot"},
}

-- canonical op key -> connective entry (built once at require time)
operators.by_key = {}
operators.by_symbol = {}
for _, op in ipairs(operators.connectives) do
    operators.by_key[op.key] = op
    for _, s in ipairs(op.symbols) do
        operators.by_symbol[s] = op
    end
    for _, s in ipairs(op.word_symbols or {}) do
        operators.by_symbol[s] = op
    end
end

return operators
