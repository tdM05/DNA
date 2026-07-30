import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_48_s15
    (hstep13 : ∠ d:a:c = ∠ b:a:c)
    (hstep14 : ∠ d:a:c = ∟)
    : ∠ b:a:c = ∟ := by
  linarith

end Elements.Book1
