import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step4_tri (a b c d : Point) (AB BC AC BD : Line)
  (hbAB : b.onLine AB) (haAB : a.onLine AB) (hab : a ≠ b)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcAC : c.onLine AC) (haAC : a.onLine AC)
  (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
  (hbd : distinctPointsOnLine b d BD)
  (hADC : between a d c)
  : formTriangle a b d AB BD AC := by
  euclid_finish

end Elements.Book1
