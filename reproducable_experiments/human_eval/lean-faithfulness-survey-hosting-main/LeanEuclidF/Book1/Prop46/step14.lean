import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_46_s14
    (a b d e : Point)
    (s12 : ∠ b:a:d + ∠ a:d:e = ∟ + ∟)
    (s13 : ∠ b:a:d = ∟) :
    ∠ a:d:e = ∟ := by
  linarith

end Elements.Book1
