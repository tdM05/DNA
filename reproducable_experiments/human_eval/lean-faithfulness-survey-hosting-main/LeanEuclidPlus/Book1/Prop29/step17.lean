import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_29_s17
    (s15 : ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d)
    (s16 : ∠ e:g:b + ∠ b:g:h = ∟ + ∟) :
    ∠ b:g:h + ∠ g:h:d = ∟ + ∟ := by linarith

end Elements.Book1
