import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step8 (a b c d : Point) (AB BC AC DC : Line)
    (hbet : between b d a)
    (hstep3 : |(d─b)| = |(a─c)|)
    (hstep6 : ∠ d:b:c = ∠ a:c:b)
    (hstep7 : |(d─c)| = |(a─b)|)
    (hd_DC : d.onLine DC) (hc_DC : c.onLine DC)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB) :
    Triangle.area △ d:b:c = Triangle.area △ a:c:b := by
  euclid_apply (proposition_4 b d c c a b AB DC BC AC AB BC)
  euclid_apply (area_congruence d b c a c b)
  euclid_finish

end Elements.Book1
