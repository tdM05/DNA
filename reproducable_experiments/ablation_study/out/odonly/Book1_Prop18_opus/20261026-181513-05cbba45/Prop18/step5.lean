import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step5 (a b c d : Point) (AB BC AC : Line)
  (h3 : ∠ a:d:b > ∠ d:c:b) (h4 : ∠ a:d:b = ∠ a:b:d)
  (hadc : between a d c)
  (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hab : a ≠ b)
  (hb_bc : b.onLine BC) (hc_bc : c.onLine BC)
  (ha_ac : a.onLine AC) (hc_ac : c.onLine AC)
  (hac_ab : AC ≠ AB) (hbc_ac : BC ≠ AC)
  : ∠ a:b:d > ∠ b:c:a := by
  have hray : ∠ d:c:b = ∠ a:c:b := by euclid_finish
  euclid_finish

end Elements.Book1
