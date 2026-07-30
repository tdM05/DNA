import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_29_s13
    (s11 : ∠ a:g:h = ∠ g:h:d)
    (s12 : ∠ a:g:h = ∠ e:g:b) :
    ∠ e:g:b = ∠ g:h:d := by linarith

end Elements.Book1
