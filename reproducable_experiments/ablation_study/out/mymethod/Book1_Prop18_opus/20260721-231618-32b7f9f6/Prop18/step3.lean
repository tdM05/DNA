import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step3 (a b c d : Point) (AB BC AC BD : Line)
  (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_ab : a ≠ b)
  (h_b_bc : b.onLine BC) (h_c_bc : c.onLine BC)
  (h_c_ac : c.onLine AC) (h_a_ac : a.onLine AC)
  (h_ab_bc : AB ≠ BC) (h_bc_ac : BC ≠ AC) (h_ac_ab : AC ≠ AB)
  (h_b_bd : b.onLine BD) (h_d_bd : d.onLine BD)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : between a d c)   -- "angle $ADB$ is external to triangle $BCD$"
  : ∠ a:d:b > ∠ d:c:b := by
  euclid_apply (proposition_16 b c d a BC AC BD)
  euclid_finish

end Elements.Book1
