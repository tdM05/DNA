import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step3 (a b c d d' : Point) (AB BC AC DC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hcBC : c.onLine BC) (haAC : a.onLine AC)
    (hcAC : c.onLine AC) (hABAC : AC ≠ AB)
    (hd'AB : d'.onLine AB) (hadd' : between a d d')
    (hdDC : d.onLine DC) (hcDC : c.onLine DC) : distinctPointsOnLine d c DC := by
  euclid_finish

end Elements.Book1
