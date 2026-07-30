import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_17_s6 (a b c d : Point)
    (s4 : ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ b:c:a)
    (s5 : ∠ a:c:d + ∠ a:c:b = ∟ + ∟) :
    ∠ a:b:c + ∠ b:c:a < ∟ + ∟ := by
  linarith

end Elements.Book1
