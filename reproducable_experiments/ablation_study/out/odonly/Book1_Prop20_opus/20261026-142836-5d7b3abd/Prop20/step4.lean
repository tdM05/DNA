import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step4 (a b c d d' : Point) (AB BC AC DC : Line)
  (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_d'AB : d'.onLine AB)
  (h_add' : between a d d')
  (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
  (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
  (h_dDC : d.onLine DC) (h_cDC : c.onLine DC)
  (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
  (h_ad_eq_ac : |(a─d)| = |(a─c)|)
  (hassump1 : |(d─a)| = |(a─c)|)
  : ∠ a:d:c = ∠ a:c:d := by
  have htri : formTriangle a d c AB DC AC := by euclid_finish
  euclid_apply (extend_point AC a c) as e
  euclid_apply (proposition_5 a d c d' e AB DC AC)
  euclid_finish

end Elements.Book1
