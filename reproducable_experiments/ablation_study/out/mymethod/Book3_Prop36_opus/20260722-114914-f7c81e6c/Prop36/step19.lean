import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step19
  (a c f : Point)
  (step19_assumption1 : |(a─f)| = |(f─c)|)
  : |(a─f)| = |(f─c)| := by
  exact step19_assumption1

end Elements.Book3
