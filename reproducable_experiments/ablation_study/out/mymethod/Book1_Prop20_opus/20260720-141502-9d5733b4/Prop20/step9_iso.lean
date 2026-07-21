import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_iso (a b c e e' : Point) (AB BC AC EC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (he'_AB : e'.onLine AB) (h_bee' : between b e e')
    (h_be_bc : |(b─e)| = |(b─c)|)
    (he_EC : e.onLine EC) (hc_EC : c.onLine EC) :
    ∠ b:e:c = ∠ b:c:e := by
  euclid_apply (extend_point BC b c) as f2
  euclid_apply (proposition_5 b e c e' f2 AB EC BC)
  euclid_finish

end Elements.Book1
