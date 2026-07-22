import SystemE
import Book1Variants.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step4 (a b c d : Point) (AB BC AC BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hACAB : AC ≠ AB)
    (hadc : between a d c)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : |(a─b)| = |(a─d)|)   -- "$AB$ is also equal to side $AD$"
    : ∠ a:d:b = ∠ a:b:d := by
  euclid_apply (proposition_5' a b d AB BD AC)
  euclid_finish

end Elements.Book1
