import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_45_s5
    (h k f g m : Point)
    (s4 : ∠ h:k:f = ∠ g:h:m) :
    ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g := by
  linarith

end Elements.Book1
