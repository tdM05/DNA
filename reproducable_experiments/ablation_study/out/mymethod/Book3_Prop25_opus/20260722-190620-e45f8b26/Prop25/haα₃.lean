import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_haα₃ (a : Point) (α₃ : Circle)
    (hae : a.onCircle α₃) :
    a.onCircle α₃ := by
  euclid_finish

end Elements.Book3
