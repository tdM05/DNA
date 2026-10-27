import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_swapfig
  (a b c : Point) (AB BC AC : Line)
  (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_anb : a ≠ b)
  (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
  (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
  (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
  (hang : ∠ a:b:c = ∠ a:c:b)
  (hne : |(a─b)| ≠ |(a─c)|)
  (hstep1 : |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)|)
  (hnotgt : ¬ (|(a─b)| > |(a─c)|))
  : (∠ a:c:b = ∠ a:b:c)
          ∧ (a ≠ c)
          ∧ (AC ≠ BC)
          ∧ (BC ≠ AB)
          ∧ (AB ≠ AC)
          ∧ (|(a─c)| ≠ |(a─b)|)
          ∧ (|(a─c)| > |(a─b)| ∨ |(a─b)| > |(a─c)|)
          ∧ (|(a─c)| > |(a─b)|) := by euclid_finish

end Elements.Book1
