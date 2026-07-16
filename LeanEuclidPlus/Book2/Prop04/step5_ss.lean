import SystemE
import Helpers.Pasch
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step5_ss (a b c d : Point) (AB BD : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hb_bd : b.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    : c.sameSide a BD := by
  have hc_ab : c.onLine AB := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have had : a ≠ d := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have hc_off_bd : ¬(c.onLine BD) := offLine_of_two_points c b d AB BD hc_ab hb_ab hcb hb_bd hd_bd hd_off_ab
  exact sameSide_of_between b c a BD hb_bd hc_off_bd (by euclid_finish)

end Elements.Book2
