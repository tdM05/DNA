import SystemE
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step6 (a b c d : Point) (AB BC AC DC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC) (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
    (h_dDC : d.onLine DC) (h_cDC : c.onLine DC)
    (h_bad : between b a d)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : ∠ b:c:d > ∠ b:d:c)   -- "$DCB$ is a triangle having the angle $BCD$ greater than $BDC$"
    : |(d─b)| > |(b─c)| := by
  have htri : formTriangle b c d BC DC AB := by euclid_finish
  euclid_apply (proposition_19 b c d BC DC AB)
  euclid_finish

end Elements.Book1
