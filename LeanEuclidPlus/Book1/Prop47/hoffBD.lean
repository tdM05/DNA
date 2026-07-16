import SystemE

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_47_hoffBD
    (a b c : Point) (AB BC AC : Line)
    (d : Point) (BD : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (h_bac : (∠ b:a:c : ℝ) = ∟)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (h_cbd : (∠ c:b:d : ℝ) = ∟)
    (hbd_len : |(b─d)| = |(b─c)|) :
    ¬a.onLine BD := by
  by_contra h
  have hbc : b ≠ c := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hoffBD_hacute : (∠ a:b:c : ℝ) < ∟ := by sorry
  by_cases hbet : between a b d
  · have hoffBD_bet : False := by sorry
    exact hoffBD_bet
  · have hoffBD_nbet : False := by sorry
    exact hoffBD_nbet

end Elements.Book1
