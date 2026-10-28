import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_sym_area (a b c d : Point) (AB BC AC DB : Line)
    (hbet : between c d a)
    (hcd : |(c─d)| = |(a─b)|)
    (hang : ∠ d:c:b = ∠ a:b:c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB) :
    Triangle.area △ d:c:b = Triangle.area △ a:b:c := by
  euclid_apply (proposition_4 c d b b a c AC DB BC AB AC BC)
  euclid_apply (area_congruence d c b a b c)
  euclid_finish

end Elements.Book1
