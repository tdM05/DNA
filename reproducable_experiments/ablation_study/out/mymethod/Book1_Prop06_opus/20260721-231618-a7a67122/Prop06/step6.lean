import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step6
  (a b c d : Point) (AB BC AC : Line)
  (hang : ∠ a:b:c = ∠ a:c:b)
  (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcAC : c.onLine AC) (haAC : a.onLine AC)
  (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
  (hbet : between b d a) :
    ∠ d:b:c = ∠ a:c:b := by
  euclid_finish

end Elements.Book1
