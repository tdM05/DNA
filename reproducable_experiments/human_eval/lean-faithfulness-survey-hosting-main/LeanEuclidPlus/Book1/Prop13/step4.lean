import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_13_s4
    (hassump1 : ∠ c:b:e = ∠ c:b:a + ∠ a:b:e) :
    ∠ c:b:e + ∠ e:b:d = ∠ c:b:a + ∠ a:b:e + ∠ e:b:d := by
  linarith

end Elements.Book1
