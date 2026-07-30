import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_45_s12
    (f g h m l : Point)
    (s11 : ∠ m:h:g = ∠ h:g:f) :
    ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l := by
  linarith

end Elements.Book1
