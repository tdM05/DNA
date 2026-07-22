import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step12 (f g h l m : Point)
    (hstep11 : ∠ m:h:g = ∠ h:g:f)
    : ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l := by
  linarith [hstep11]

end Elements.Book1
