import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step6 (a b c d : Point) (AB BC AC BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hadc : between a d c)
    (hstep5 : ∠ a:b:d > ∠ b:c:a) :
    ∠ a:b:c > ∠ b:c:a := by
  euclid_finish

end Elements.Book1
