import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step6 (a d g h : Point)
    (hstep4 : |(a─g)| > |(g─h)|) (hstep5 : |(a─g)| = |(g─d)|) :
    |(g─d)| > |(g─h)| := by
  linarith

end Elements.Book3
