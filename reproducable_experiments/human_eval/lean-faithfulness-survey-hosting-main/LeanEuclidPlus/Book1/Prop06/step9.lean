import SystemE
import Book1.Prop04.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_6_s9 (a b c d : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (hbda : between b d a) (hbdac : |(b─d)| = |(a─c)|)
    (hdbc_acb : ∠ d:b:c = ∠ a:c:b)
    (hcong : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a)) :
    False := by
  have hoff : ¬c.onLine AB := by euclid_finish
  have heq : Triangle.area △d:b:c = Triangle.area △a:c:b := by
    euclid_apply (area_congruence d b c a c b)
    assumption
  have hdec : Triangle.area △a:d:c + Triangle.area △c:d:b = Triangle.area △a:c:b := by
    euclid_apply (sum_areas_if a b d c AB)
    assumption
  have hpos : (0 : ℝ) < Triangle.area △a:d:c := by euclid_finish
  have hsymm : Triangle.area △c:d:b = Triangle.area △d:b:c := by euclid_finish
  linarith

end Elements.Book1
