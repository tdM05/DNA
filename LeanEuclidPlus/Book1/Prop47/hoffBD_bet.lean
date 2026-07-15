import SystemE
import Book1.Prop13.Main

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_47_hoffBD_bet
    (a b c d : Point) (AB BC BD : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (h : a.onLine BD) (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hABBC : AB ≠ BC)
    (hbc : b ≠ c)
    (h_cbd : (∠ c:b:d : ℝ) = ∟)
    (hbet : between a b d)
    (hacute : (∠ a:b:c : ℝ) < ∟) :
    False := by
  euclid_apply (proposition_13 c b a d BC BD)
  euclid_finish

end Elements.Book1
