import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step10
  (a b c : Point)
  (habsurd : ¬ (|(a─b)| ≠ |(a─c)|)) :
    ¬ (|(a─b)| ≠ |(a─c)|) := by
  exact habsurd

end Elements.Book1
