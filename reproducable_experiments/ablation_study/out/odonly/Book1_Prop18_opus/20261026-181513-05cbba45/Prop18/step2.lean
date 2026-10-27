import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step2 (a b c d : Point) (AB AC BD : Line)
  (hb_bd : b.onLine BD) (hd_bd : d.onLine BD)
  (hadc : between a d c)
  (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hab : a ≠ b)
  (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hac_ab : AC ≠ AB) :
  distinctPointsOnLine b d BD := by
  euclid_finish

end Elements.Book1
