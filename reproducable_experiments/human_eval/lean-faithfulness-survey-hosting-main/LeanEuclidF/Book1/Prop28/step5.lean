import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_28_s5
    (hstep4 : ∠ a:g:h + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d) :
    ∠ a:g:h + ∠ b:g:h - ∠ b:g:h = ∠ b:g:h + ∠ g:h:d - ∠ b:g:h := by
  linarith

end Elements.Book1
