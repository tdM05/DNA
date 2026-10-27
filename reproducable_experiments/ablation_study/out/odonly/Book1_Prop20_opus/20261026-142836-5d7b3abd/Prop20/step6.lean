import SystemE
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step6 (a b c d d' : Point) (AB BC AC DC : Line)
  (h_aAB : a.onLine AB) (h_bAB : b.onLine AB)
  (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
  (h_cDC : c.onLine DC) (h_dDC : d.onLine DC)
  (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
  (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
  (step1 : between b a d)
  (hassump1 : ∠ b:c:d > ∠ b:d:c)
  : |(d─b)| > |(b─c)| := by
  have htri : formTriangle b c d BC DC AB := by euclid_finish
  euclid_apply (proposition_19 b c d BC DC AB)
  euclid_finish

end Elements.Book1
