import SystemE
import Book1.Prop03.Main
import Book1.Prop04.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_6_x2 (a b c : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (hang : ∠ a:b:c = ∠ a:c:b) (hgt : |(a─c)| > |(a─b)|) :
    False := by
  euclid_apply (proposition_3 c a a b AC AB) as e
  euclid_apply (line_from_points e b) as EB
  have h1 : ∠ e:c:b = ∠ a:c:b := by
    euclid_apply (equal_angles c e a b b AC BC)
    assumption
  have h6 : ∠ e:c:b = ∠ a:b:c := h1.trans hang.symm
  have h8 : |(e─b)| = |(a─c)| ∧ (∠ c:e:b = ∠ b:a:c) ∧ (∠ c:b:e = ∠ b:c:a) := by
    euclid_apply (proposition_4 c e b b a c AC EB BC AB AC BC)
    (try split_ands) <;> assumption
  have hoff : ¬b.onLine AC := by euclid_finish
  have heq : Triangle.area △c:e:b = Triangle.area △c:a:b := by
    euclid_apply (area_congruence c e b c a b)
    assumption
  have hdec : Triangle.area △c:e:b + Triangle.area △b:e:a = Triangle.area △c:b:a := by
    euclid_apply (sum_areas_if c a e b AC)
    assumption
  have hpos : (0 : ℝ) < Triangle.area △b:e:a := by euclid_finish
  have hsymm : Triangle.area △c:b:a = Triangle.area △c:a:b := area_symm_2 c b a
  linarith

end Elements.Book1
