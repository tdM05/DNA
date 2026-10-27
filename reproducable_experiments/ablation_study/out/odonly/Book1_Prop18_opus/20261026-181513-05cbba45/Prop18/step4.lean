import SystemE
import Book1Variants.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step4 (a b c d : Point) (AB AC BD : Line)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(a─b)| = |(a─d)|)   -- "$AB$ is also equal to side $AD$"
  (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hab : a ≠ b)
  (hb_bd : b.onLine BD) (hd_bd : d.onLine BD)
  (hadc : between a d c)
  (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hac_ab : AC ≠ AB)
  : ∠ a:d:b = ∠ a:b:d := by
  euclid_apply (proposition_5' a b d AB BD AC)
  euclid_finish

end Elements.Book1
