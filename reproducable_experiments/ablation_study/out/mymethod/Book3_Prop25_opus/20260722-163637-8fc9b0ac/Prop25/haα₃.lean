import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_haα₃ (a : Point) (α₃ : Circle)
    (ha_circle : a.onCircle α₃) :
    a.onCircle α₃ := by
  exact ha_circle

end Elements.Book3
