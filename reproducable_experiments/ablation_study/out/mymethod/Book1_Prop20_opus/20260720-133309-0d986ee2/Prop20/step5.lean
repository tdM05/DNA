import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step5 (a b c d : Point) (AB BC AC DC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC) (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
    (h_dDC : d.onLine DC) (h_cDC : c.onLine DC)
    (h_bad : between b a d) (h_adc_eq : ∠ a:d:c = ∠ a:c:d)
    : ∠ b:c:d > ∠ a:d:c := by
  euclid_apply (pasch_2 b a d BC)
  euclid_apply (pasch_2 d a b DC)
  euclid_apply (sum_angles_onlyif c b d a BC DC)
  euclid_finish

end Elements.Book1
