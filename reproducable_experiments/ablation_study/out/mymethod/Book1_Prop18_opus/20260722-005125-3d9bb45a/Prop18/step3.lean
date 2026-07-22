import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step3 (a b c d : Point) (AB BC AC BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : between a d c)   -- "angle $ADB$ is external to triangle $BCD$"
    : ∠ a:d:b > ∠ d:c:b := by
  euclid_apply (proposition_16 b c d a BC AC BD)
  euclid_finish

end Elements.Book1
