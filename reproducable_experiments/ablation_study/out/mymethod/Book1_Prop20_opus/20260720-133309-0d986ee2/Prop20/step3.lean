import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step3 (a b c d d' : Point) (AB BC AC DC : Line)
    (h_dDC : d.onLine DC) (h_cDC : c.onLine DC)
    (h_add' : between a d d') (h_aAB : a.onLine AB) (h_d'AB : d'.onLine AB)
    (h_cBC : c.onLine BC) (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ACAB : AC ≠ AB) : distinctPointsOnLine d c DC := by
  euclid_finish

end Elements.Book1
