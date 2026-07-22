import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step7
  (a b c d : Point) (AB BC AC DC : Line)
  (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcAC : c.onLine AC) (haAC : a.onLine AC)
  (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
  (hbet : between b d a)
  (hdDC : d.onLine DC) (hcDC : c.onLine DC)
  (hstep5 : |(d─b)| = |(a─c)| ∧ |(b─c)| = |(c─b)|)
  (hangle : ∠ d:b:c = ∠ a:c:b) :
    |(d─c)| = |(a─b)| := by
  obtain ⟨hdb, hbc⟩ := hstep5
  euclid_apply (proposition_4 b d c c a b AB DC BC AC AB BC)
  euclid_finish

end Elements.Book1
