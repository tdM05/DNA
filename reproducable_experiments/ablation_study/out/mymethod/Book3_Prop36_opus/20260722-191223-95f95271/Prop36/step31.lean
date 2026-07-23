import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step31
  (a b c d : Point)
  (hstep30 : |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)|)
  : |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)| := by
  exact hstep30

end Elements.Book3
