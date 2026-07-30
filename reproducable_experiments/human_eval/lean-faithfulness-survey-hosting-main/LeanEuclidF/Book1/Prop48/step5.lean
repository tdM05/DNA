import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_48_s5
    (hstep4 : |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|)
    : |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(a─b)| * |(a─b)| + |(a─c)| * |(a─c)| := by
  linarith

end Elements.Book1
