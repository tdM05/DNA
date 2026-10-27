import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step3 (a b c d : Point) (AB BC AC BD : Line)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : between a d c)   -- "angle $ADB$ is external to triangle $BCD$"
  (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hab : a ≠ b)
  (hb_bc : b.onLine BC) (hc_bc : c.onLine BC)
  (hc_ac : c.onLine AC) (ha_ac : a.onLine AC)
  (hb_bd : b.onLine BD) (hd_bd : d.onLine BD)
  (hab_bc : AB ≠ BC) (hbc_ac : BC ≠ AC) (hac_ab : AC ≠ AB)
  : ∠ a:d:b > ∠ d:c:b := by
  euclid_apply (proposition_16 b c d a BC AC BD)
  euclid_finish

end Elements.Book1
