import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step6
  (a b c d : Point) (AB BC AC : Line)
  (hbet : between b d a)
  (hang : ∠ a:b:c = ∠ a:c:b)
  (haAB : a.onLine AB) (hbAB : b.onLine AB)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcAC : c.onLine AC) (haAC : a.onLine AC)
  (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
  (hab : a ≠ b)
  : ∠ d:b:c = ∠ a:c:b := by
  have hdbc : ∠ d:b:c = ∠ a:b:c := by
    euclid_apply (equal_angles b d a c c AB BC)
    euclid_finish
  rw [hdbc]; exact hang

end Elements.Book1
