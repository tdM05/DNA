import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_swapfig
  (a b c : Point) (AB BC AC : Line)
  (hang : ∠ a:b:c = ∠ a:c:b)
  (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcAC : c.onLine AC) (haAC : a.onLine AC)
  (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
  (hne : |(a─b)| ≠ |(a─c)|)
  (hstep1 : |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)|)
  (hgt : ¬ |(a─b)| > |(a─c)|)
  : (∠ a:c:b = ∠ a:b:c)
          ∧ (a ≠ c)
          ∧ (AC ≠ BC)
          ∧ (BC ≠ AB)
          ∧ (AB ≠ AC)
          ∧ (|(a─c)| ≠ |(a─b)|)
          ∧ (|(a─c)| > |(a─b)| ∨ |(a─b)| > |(a─c)|)
          ∧ (|(a─c)| > |(a─b)|) := by
  euclid_finish

end Elements.Book1
