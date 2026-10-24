local automata = {}

require "automata.basic"(automata)
require "automata.dfa_nfa"(automata)
require "automata.pda"(automata)
require "automata.regexp"(automata)
require "automata.token_sequence"(automata)
require "automata.state_set"(automata)
require "automata.word_problem"(automata)
require "automata.word_generator"(automata)
require "automata.word_problem_dfa_nfa"(automata)
require "automata.word_problem_pda"(automata)
require "automata.grammar"(automata)
require "automata.grammar_tools"(automata)
require "automata.algorithms"(automata)

return automata
