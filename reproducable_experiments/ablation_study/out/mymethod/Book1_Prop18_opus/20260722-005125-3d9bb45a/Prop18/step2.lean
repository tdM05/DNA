import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step2 (a b c d : Point) (AB BC AC BD : Line)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hadc : between a d c)
    (hABAC : AC ≠ AB) : distinctPointsOnLine b d BD := by
  euclid_finish

end Elements.Book1
