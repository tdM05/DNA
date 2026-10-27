import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step6 (a b c d : Point) (AB BC AC BD : Line)
  (hbAB : b.onLine AB) (haAB : a.onLine AB) (hab : a ≠ b)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcAC : c.onLine AC) (haAC : a.onLine AC)
  (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB) (hABBC : AB ≠ BC)
  (hbd : distinctPointsOnLine b d BD)
  (hADC : between a d c)
  (step5 : ∠ a:b:d > ∠ b:c:a)
  : ∠ a:b:c > ∠ b:c:a := by
  euclid_finish

end Elements.Book1
