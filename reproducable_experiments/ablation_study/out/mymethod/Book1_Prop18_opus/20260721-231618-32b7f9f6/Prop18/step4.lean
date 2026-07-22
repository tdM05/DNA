import SystemE
import Book1Variants.Prop05
import Book1.Prop18.step4_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step4 (a b c d : Point) (AB BC AC BD : Line)
  (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_ab : a ≠ b)
  (h_b_bd : b.onLine BD) (h_d_bd : d.onLine BD)
  (h_a_ac : a.onLine AC) (h_c_ac : c.onLine AC) (h_ac_ab : AC ≠ AB)
  (h_adc : between a d c)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(a─b)| = |(a─d)|)   -- "$AB$ is also equal to side $AD$"
  : ∠ a:d:b = ∠ a:b:d := by
  have step4_tri : formTriangle a b d AB BD AC := by euclid_apply (helper_1_18_step4_tri a b c d AB BC AC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between a d c; assumption)))
  euclid_apply (proposition_5' a b d AB BD AC)
  euclid_finish

end Elements.Book1
