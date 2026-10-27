import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step11 (a b c : Point)
  (step10 : ¬ (|(a─b)| ≠ |(a─c)|))
  : |(a─b)| = |(a─c)| := by exact not_not.mp step10

end Elements.Book1
