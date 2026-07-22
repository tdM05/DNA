import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step11
  (a b c : Point)
  (hstep10 : ¬ (|(a─b)| ≠ |(a─c)|)) :
    |(a─b)| = |(a─c)| := by
  by_contra h
  exact hstep10 h

end Elements.Book1
