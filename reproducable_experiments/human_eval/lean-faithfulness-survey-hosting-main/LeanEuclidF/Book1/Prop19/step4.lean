import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_19_s4
    (h_gt : ∠ a:b:c > ∠ b:c:a)
    (h_eq : ∠ a:b:c = ∠ b:c:a) :
    False := by
  linarith

end Elements.Book1
