import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_swapfig (a b c : Point) (AB BC AC : Line)
  (right : ∠a:b:c = ∠a:c:b)
  (left_2a : a.onLine AB) (left_3 : b.onLine AB) (right_3 : a ≠ b)
  (left_2 : b.onLine BC) (left_4 : c.onLine BC)
  (left_5 : c.onLine AC) (left_6 : a.onLine AC)
  (left_7 : AB ≠ BC) (left_8 : BC ≠ AC) (right_8 : AC ≠ AB)
  (hne : |(a─b)| ≠ |(a─c)|)
  (step1 : |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)|)
  (hgt : ¬|(a─b)| > |(a─c)|)
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
