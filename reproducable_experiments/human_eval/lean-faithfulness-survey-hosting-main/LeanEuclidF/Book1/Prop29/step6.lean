import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_29_s6
    (s4 : ∠ a:g:h + ∠ b:g:h > ∠ b:g:h + ∠ g:h:d)
    (s5 : ∠ a:g:h + ∠ b:g:h = ∟ + ∟) :
    ∠ b:g:h + ∠ g:h:d < ∟ + ∟ := by
  linarith

end Elements.Book1
