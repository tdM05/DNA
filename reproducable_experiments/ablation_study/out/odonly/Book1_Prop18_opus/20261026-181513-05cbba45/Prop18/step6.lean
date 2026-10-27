import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step6 (a b c d : Point) (AB BC AC BD : Line)
  (h5 : ∠ a:b:d > ∠ b:c:a)
  (hadc : between a d c)
  (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hab : a ≠ b)
  (hb_bc : b.onLine BC) (hc_bc : c.onLine BC)
  (ha_ac : a.onLine AC) (hc_ac : c.onLine AC)
  (hb_bd : b.onLine BD) (hd_bd : d.onLine BD)
  (hab_bc : AB ≠ BC) (hbc_ac : BC ≠ AC) (hac_ab : AC ≠ AB)
  : ∠ a:b:c > ∠ b:c:a := by
  have hsplit : ∠ a:b:c = ∠ a:b:d + ∠ d:b:c := by euclid_finish
  have hpos : ∠ d:b:c > 0 := by euclid_finish
  euclid_finish

end Elements.Book1
