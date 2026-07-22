import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step5 (a b c d : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hACAB : AC ≠ AB)
    (hstep3 : ∠ a:d:b > ∠ d:c:b) (hstep4 : ∠ a:d:b = ∠ a:b:d)
    (hadc : between a d c) : ∠ a:b:d > ∠ b:c:a := by
  have hray : ∠ d:c:b = ∠ b:c:a := by euclid_finish
  linarith

end Elements.Book1
