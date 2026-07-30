import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_13_s6
    (hassump1 : ∠ d:b:a = ∠ d:b:e + ∠ e:b:a) :
    ∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c := by
  linarith

end Elements.Book1
