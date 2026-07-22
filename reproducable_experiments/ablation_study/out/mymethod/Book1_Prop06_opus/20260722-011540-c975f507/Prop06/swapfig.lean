import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_swapfig (a b c : Point) (AB BC AC : Line)
  (hangle : ∠ a:b:c = ∠ a:c:b)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab : a ≠ b)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
  (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
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
