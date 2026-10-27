import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step8
  (a b c d : Point) (AB BC AC DC : Line)
  (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_anb : a ≠ b)
  (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
  (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
  (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
  (h_dDC : d.onLine DC) (h_cDC : c.onLine DC)
  (hbet : between b d a)
  (hbd : |(b─d)| = |(a─c)|)
  (hang6 : ∠ d:b:c = ∠ a:c:b)
  : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a) := by
  euclid_apply (proposition_4 b d c c a b AB DC BC AC AB BC)
  euclid_finish

end Elements.Book1
