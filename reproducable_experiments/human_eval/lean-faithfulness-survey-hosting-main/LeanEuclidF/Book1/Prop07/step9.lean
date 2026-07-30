import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_7_s9 (c d b : Point)
    (s7 : ∠ c:d:b = ∠ d:c:b)
    (s8 : ∠ c:d:b > ∠ d:c:b)
    : False := by linarith

end Elements.Book1
