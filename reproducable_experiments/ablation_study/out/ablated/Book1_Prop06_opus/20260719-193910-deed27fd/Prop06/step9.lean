import SystemE

namespace Elements.Book1

theorem helper_1_6_step9 (a b c d : Point) (AB BC AC DC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB)
    (hbetween : between b d a)
    (hbd : |(b─d)| = |(a─c)|)
    (hgt : |(a─b)| > |(a─c)|)
    (hd_DC : d.onLine DC) (hc_DC : c.onLine DC)
    (hang : ∠ a:b:c = ∠ a:c:b)
    (hstep8 : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a)) :
    False := by
  euclid_finish

end Elements.Book1
