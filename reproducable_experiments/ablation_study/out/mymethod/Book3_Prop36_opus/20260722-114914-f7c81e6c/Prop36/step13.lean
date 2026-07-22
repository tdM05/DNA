import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step13
  (e : Point) (ABC : Circle)
  (he : e.isCentre ABC)
  : e.isCentre ABC := by
  exact he

end Elements.Book3
