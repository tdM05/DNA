import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step4 (a b c d d' : Point) (AB BC AC DC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC) (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
    (h_d'AB : d'.onLine AB) (h_bad' : between b a d') (h_add' : between a d d')
    (h_adac : |(a─d)| = |(a─c)|)
    (h_dDC : d.onLine DC) (h_cDC : c.onLine DC)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : |(d─a)| = |(a─c)|)   -- "$DA$ is equal to $AC$"
    : ∠ a:d:c = ∠ a:c:d := by
  euclid_apply (extend_point AC a c) as e
  have htri : formTriangle a d c AB DC AC := by euclid_finish
  euclid_apply (proposition_5 a d c d' e AB DC AC)
  euclid_finish

end Elements.Book1
