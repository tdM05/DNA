import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_6_s11 (a b c : Point) (habsurd : ¬ (|(a─b)| ≠ |(a─c)|)) :
    |(a─b)| = |(a─c)| := by
  by_contra h
  exact habsurd h

end Elements.Book1
