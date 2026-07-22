import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step2 (a b c d : Point) (AB BC AC BD : Line)
  (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_ab : a ≠ b)
  (h_c_ac : c.onLine AC) (h_a_ac : a.onLine AC) (h_ac_ab : AC ≠ AB)
  (h_adc : between a d c)
  (h_b_bd : b.onLine BD) (h_d_bd : d.onLine BD) :
  distinctPointsOnLine b d BD := by
  euclid_finish

end Elements.Book1
