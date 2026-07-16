import SystemE
import Helpers.OffLine
import Helpers.Parallel
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step14_assumption1 (a b c d e : Point) (AB CF AD BE : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_be : b.onLine BE) (he_be : e.onLine BE)
    (hang : ∠ b:a:d = ∟) (hang_e : ∠ a:b:e = ∟)
    (had_len : |(a─d)| = |(a─b)|) (hbe_len : |(b─e)| = |(a─b)|)
    (hCF_AD : ¬(CF.intersectsLine AD)) (hAD_BE : ¬(AD.intersectsLine BE))
    : ¬(CF.intersectsLine BE) := by
  have had : a ≠ d := by euclid_finish
  have hbe : b ≠ e := by euclid_finish
  have hc_ab : c.onLine AB := by euclid_finish
  have hca : c ≠ a := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have he_off_ab : ¬(e.onLine AB) := offLine_of_right_angle b a e AB hb_ab ha_ab (Ne.symm hab) hbe hang_e
  have hc_off_ad : ¬(c.onLine AD) := offLine_of_two_points c a d AB AD hc_ab ha_ab hca ha_ad hd_ad hd_off_ab
  have ha_off_be : ¬(a.onLine BE) := offLine_of_two_points a b e AB BE ha_ab hb_ab hab hb_be he_be he_off_ab
  have hc_off_be : ¬(c.onLine BE) := offLine_of_two_points c b e AB BE hc_ab hb_ab hcb hb_be he_be he_off_ab
  have hCF_ne_AD : CF ≠ AD := line_ne_of_offLine c CF AD hc_cf hc_off_ad
  have hAD_ne_BE : AD ≠ BE := line_ne_of_offLine a AD BE ha_ad ha_off_be
  have hCF_ne_BE : CF ≠ BE := line_ne_of_offLine c CF BE hc_cf hc_off_be
  exact not_intersects_trans CF AD BE hCF_AD hAD_BE hCF_ne_AD hAD_ne_BE hCF_ne_BE

end Elements.Book2
