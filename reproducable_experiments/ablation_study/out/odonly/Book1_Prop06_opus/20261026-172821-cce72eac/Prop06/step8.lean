import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step8 (a b c d : Point) (AB BC AC DC : Line)
  (left_2a : a.onLine AB) (left_3 : b.onLine AB)
  (left_2 : b.onLine BC) (left_4 : c.onLine BC)
  (left_5 : c.onLine AC) (left_6 : a.onLine AC)
  (left_7 : AB ≠ BC) (left_8 : BC ≠ AC) (right_8 : AC ≠ AB)
  (hbda : between b d a)
  (hdDC : d.onLine DC) (hcDC : c.onLine DC)
  (step5 : |(d─b)| = |(a─c)| ∧ |(b─c)| = |(c─b)|)
  (step6 : ∠ d:b:c = ∠ a:c:b)
  : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a) := by
  euclid_apply (proposition_4 b d c c a b AB DC BC AC AB BC)
  euclid_finish

end Elements.Book1
