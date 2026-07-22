import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step9 (a f g : Point)
  (habsurd1 : ¬(¬(between f g a)))
  : between f g a := by
  by_contra h
  exact habsurd1 h

end Elements.Book3
