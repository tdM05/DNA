import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_gt (a b c e e' : Point) (AB BC AC EC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (he'_AB : e'.onLine AB) (h_abe' : between a b e') (h_bee' : between b e e')
    (he_EC : e.onLine EC) (hc_EC : c.onLine EC)
    (hstep9_iso : ∠ b:e:c = ∠ b:c:e) :
    ∠ a:c:e > ∠ b:e:c := by
  have hsame1 : a.sameSide b EC := by euclid_finish
  have hsame2 : e.sameSide b AC := by euclid_finish
  euclid_apply (sum_angles_onlyif c a e b AC EC)
  euclid_finish

end Elements.Book1
