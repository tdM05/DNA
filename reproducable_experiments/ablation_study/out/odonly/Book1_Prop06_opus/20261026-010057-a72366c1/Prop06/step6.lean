import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step6
  (a b c d : Point) (AB BC AC : Line)
  (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_anb : a ≠ b)
  (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
  (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
  (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
  (hbet : between b d a)
  (hang : ∠ a:b:c = ∠ a:c:b)
  : ∠ d:b:c = ∠ a:c:b := by euclid_finish

end Elements.Book1
