import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step4 (a f g h : Point)
  (h_bet_fgh : between f g h)
  (step3 : |(a─g)| > |(f─h)| - |(g─f)|)
  : |(a─g)| > |(g─h)| := by
  have hbet : |(f─h)| = |(f─g)| + |(g─h)| := by clear step3; euclid_finish
  have hsym : |(f─g)| = |(g─f)| := by clear step3; euclid_finish
  linarith [step3, hbet, hsym]

end Elements.Book3
