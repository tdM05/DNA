import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step15 (f g h l m : Point)
    (hstep13 : ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l)
    (hstep14 : ∠ m:h:g + ∠ h:g:l = ∟ + ∟)
    : ∠ h:g:f + ∠ h:g:l = ∟ + ∟ := by
  linarith [hstep13, hstep14]

end Elements.Book1
