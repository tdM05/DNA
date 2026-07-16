import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Parallel
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step9_par (a b c d e g k : Point) (AB CF AD BD BE HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hb_be : b.onLine BE) (hk_be : k.onLine BE) (he_be : e.onLine BE)
    (hg_hk : g.onLine HK) (hk_hk : k.onLine HK)
    (hang : ∠ b:a:d = ∟) (hang_e : ∠ a:b:e = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hbe_len : |(b─e)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hAD_BE : ¬(AD.intersectsLine BE))
    (hassump1 : ¬(CF.intersectsLine AD))
    : formParallelogram c b g k AB HK CF BE := by
  have step5_bgd : between b g d := by sorry
  have had : a ≠ d := by euclid_finish
  have hc_ab : c.onLine AB := by euclid_finish
  have hca : c ≠ a := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have hgb : g ≠ b := by euclid_finish
  have hbe : b ≠ e := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have he_off_ab : ¬(e.onLine AB) := offLine_of_right_angle b a e AB hb_ab ha_ab (Ne.symm hab) hbe hang_e
  have hc_off_ad : ¬(c.onLine AD) := offLine_of_two_points c a d AB AD hc_ab ha_ab hca ha_ad hd_ad hd_off_ab
  have ha_off_bd : ¬(a.onLine BD) := offLine_of_two_points a b d AB BD ha_ab hb_ab hab hb_bd hd_bd hd_off_ab
  have hg_off_ab : ¬(g.onLine AB) := offLine_of_two_points g b a BD AB hg_bd hb_bd hgb hb_ab ha_ab ha_off_bd
  have hc_off_be : ¬(c.onLine BE) := offLine_of_two_points c b e AB BE hc_ab hb_ab hcb hb_be he_be he_off_ab
  have ha_off_be : ¬(a.onLine BE) := offLine_of_two_points a b e AB BE ha_ab hb_ab hab hb_be he_be he_off_ab
  have hb_off_cf : ¬(b.onLine CF) := offLine_of_two_points b c g AB CF hb_ab hc_ab hbc hc_cf hg_cf hg_off_ab
  have hHK_ne_AB : HK ≠ AB := line_ne_of_offLine g HK AB hg_hk hg_off_ab
  have hb_off_hk : ¬(b.onLine HK) := offLine_of_parallel_simple' b AB HK hb_ab (Ne.symm hHK_ne_AB) hHK_AB
  have hbk : b ≠ k := by euclid_finish
  have hCF_ne_AD : CF ≠ AD := line_ne_of_offLine c CF AD hc_cf hc_off_ad
  have hAD_ne_BE : AD ≠ BE := line_ne_of_offLine a AD BE ha_ad ha_off_be
  have hCF_ne_BE : CF ≠ BE := line_ne_of_offLine c CF BE hc_cf hc_off_be
  have hCF_BE : ¬(CF.intersectsLine BE) := not_intersects_trans CF AD BE hassump1 hAD_BE hCF_ne_AD hAD_ne_BE hCF_ne_BE
  have hBE_CF : ¬(BE.intersectsLine CF) := fun h => hCF_BE (intersection_symm BE CF h)
  have hcsg : c.sameSide g BE := sameSide_of_parallel c g b CF BE hc_cf hg_cf hb_be hb_off_cf hBE_CF
  have hAB_HK : ¬(AB.intersectsLine HK) := fun h => hHK_AB (intersection_symm AB HK h)
  euclid_finish

end Elements.Book2
