import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step3_tri (a b c d : Point) (AB BC AC BD : Line)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hbAB : b.onLine AB) (haAB : a.onLine AB) (hab : a ≠ b)
  (hcAC : c.onLine AC) (haAC : a.onLine AC)
  (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
  (hbd : distinctPointsOnLine b d BD)
  (hADC : between a d c)
  : formTriangle b c d BC AC BD := by
  euclid_finish

end Elements.Book1
