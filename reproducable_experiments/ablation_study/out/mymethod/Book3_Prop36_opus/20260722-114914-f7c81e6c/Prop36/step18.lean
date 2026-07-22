import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step18
  (a c f : Point)
  (step17 : |(a─f)| = |(f─c)|)
  : |(a─f)| = |(f─c)| := by
  exact step17

end Elements.Book3
