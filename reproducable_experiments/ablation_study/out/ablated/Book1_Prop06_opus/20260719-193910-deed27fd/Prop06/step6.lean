import SystemE

namespace Elements.Book1

theorem helper_1_6_step6 (a b c d : Point) (AB BC AC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB)
    (hbetween : between b d a)
    (hang : ∠ a:b:c = ∠ a:c:b) :
    ∠ d:b:c = ∠ a:c:b := by
  euclid_finish

end Elements.Book1
