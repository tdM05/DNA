import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step3 (a b c d d' : Point) (AB BC AC DC : Line)
  (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_d'AB : d'.onLine AB) (h_ab_ne : a ≠ b)
  (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
  (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
  (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
  (h_add' : between a d d')
  (hdDC : d.onLine DC) (hcDC : c.onLine DC) : distinctPointsOnLine d c DC := by
  euclid_finish

end Elements.Book1
