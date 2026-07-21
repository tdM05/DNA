import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step5 (a b c d : Point) (AB BC AC DC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hd_DC : d.onLine DC) (hc_DC : c.onLine DC)
    (hstep1 : between b a d) (hstep4 : ∠ a:d:c = ∠ a:c:d) :
    ∠ b:c:d > ∠ a:d:c := by
  have hsame1 : b.sameSide a DC := by euclid_finish
  have hsame2 : d.sameSide a BC := by euclid_finish
  euclid_apply (sum_angles_onlyif c b d a BC DC)
  euclid_finish

end Elements.Book1
