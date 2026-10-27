import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step4 (a b c d d' : Point) (AB BC AC DC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
    (h_dpAB : d'.onLine AB) (h_add' : between a d d')
    (h_dDC : d.onLine DC) (h_cDC : c.onLine DC)
    (hassump1 : |(d─a)| = |(a─c)|) :
    ∠ a:d:c = ∠ a:c:d := by
  euclid_apply (extend_point AB a d) as x
  euclid_apply (extend_point AC a c) as y
  euclid_apply (proposition_5 a d c x y AB DC AC)
  euclid_finish

end Elements.Book1
