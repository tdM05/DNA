import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_29_s14 :
    ∠ e:g:b = ∠ g:h:d → ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d := by
  intro h; linarith

end Elements.Book1
