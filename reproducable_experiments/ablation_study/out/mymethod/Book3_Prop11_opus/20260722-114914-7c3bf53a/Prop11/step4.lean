import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step4 (a f g h : Point)
    (hbet : between f g h)
    (hstep3 : |(a─g)| > |(f─h)| - |(g─f)|) :
    |(a─g)| > |(g─h)| := by
  have hlen : |(f─h)| = |(g─f)| + |(g─h)| := by
    clear hstep3
    euclid_finish
  linarith

end Elements.Book3
