import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step9
  (a b c d : Point) (AB BC AC : Line)
  (hstep8 : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a))
  (hbet : between b d a)
  (hang : ∠ a:b:c = ∠ a:c:b)
  (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_anb : a ≠ b)
  (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
  (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
  (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
  : False := by euclid_finish

end Elements.Book1
