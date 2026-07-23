import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step10 (a b c d f : Point)
  (step9 : |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)|)
  : |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)| := by
  linarith

end Elements.Book3
