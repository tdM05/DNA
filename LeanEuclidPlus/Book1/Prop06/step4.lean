import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step4 (a b c d : Point) (AB BC AC DC : Line)
    (hd_DC : d.onLine DC) (hc_DC : c.onLine DC)
    (hbet : between b d a)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC) (hAC_AB : AC ≠ AB) :
    distinctPointsOnLine d c DC := by
  euclid_finish

end Elements.Book1
