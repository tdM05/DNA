import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step5 (a b c d : Point)
  (h_bd : |(b─d)| = |(a─c)|)
  : |(d─b)| = |(a─c)| ∧ |(b─c)| = |(c─b)| := by euclid_finish

end Elements.Book1
