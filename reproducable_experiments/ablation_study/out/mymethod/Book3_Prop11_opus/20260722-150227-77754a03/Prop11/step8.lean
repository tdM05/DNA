import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step8 (a f g : Point)
  (habsurd1 : ¬(¬(between f g a)))
  : ¬(¬(between f g a)) := by
  exact habsurd1

end Elements.Book3
