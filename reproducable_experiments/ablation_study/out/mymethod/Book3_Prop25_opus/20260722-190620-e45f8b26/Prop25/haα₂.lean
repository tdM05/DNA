import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_haα₂ (a : Point) (α₂ : Circle)
    (hae : a.onCircle α₂) :
    a.onCircle α₂ := by
  euclid_finish

end Elements.Book3
