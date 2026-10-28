import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_sym_false (a b c d : Point) (AB BC AC : Line)
    (hbet : between c d a)
    (hsym_area : Triangle.area △ d:c:b = Triangle.area △ a:b:c)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB) :
    False := by
  euclid_apply (sum_areas_if c a d b AC)
  euclid_finish

end Elements.Book1
