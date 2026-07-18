import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step4 (a b c d e f g : Point) (AB BC AC : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
    (h_bga : between b g a) (h_ang : ∠ a:b:c = ∠ d:e:f) :
    ∠ g:b:c = ∠ d:e:f := by
  have h1 : ∠ g:b:c = ∠ a:b:c := by euclid_finish
  euclid_finish

end Elements.Book1
