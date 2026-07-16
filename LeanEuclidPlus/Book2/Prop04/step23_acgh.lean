import SystemE
import Helpers.OffLine
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step23_acgh (a b c d g h : Point) (AB CF AD BD HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD) (hh_ad : h.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hg_hk : g.onLine HK) (hh_hk : h.onLine HK)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hassump1 : ¬(CF.intersectsLine AD))
    : formParallelogram a c h g AB HK AD CF := by
  have step5_bgd : between b g d := by sorry
  have had : a ≠ d := by euclid_finish
  have hgd : g ≠ d := by euclid_finish
  have hgb : g ≠ b := by euclid_finish
  have hc_ab : c.onLine AB := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have ha_off_bd : ¬(a.onLine BD) := offLine_of_two_points a b d AB BD ha_ab hb_ab hab hb_bd hd_bd hd_off_ab
  have hg_off_ad : ¬(g.onLine AD) := offLine_of_two_points g d a BD AD hg_bd hd_bd hgd hd_ad ha_ad ha_off_bd
  have hg_off_ab : ¬(g.onLine AB) := offLine_of_two_points g b a BD AB hg_bd hb_bd hgb hb_ab ha_ab ha_off_bd
  have hh_off_cf : ¬(h.onLine CF) := offLine_of_parallel h g AD CF hh_ad hg_cf hg_off_ad hassump1
  have hAD_ne_CF : AD ≠ CF := line_ne_of_offLine h AD CF hh_ad hh_off_cf
  have hAD_CF : ¬(AD.intersectsLine CF) := fun x => hassump1 (intersection_symm AD CF x)
  have hah_ss : a.sameSide h CF := sameSide_of_parallel_both a h AD CF ha_ad hh_ad hAD_ne_CF hAD_CF
  have hcg : c ≠ g := by euclid_finish
  have hAB_HK : ¬(AB.intersectsLine HK) := fun x => hHK_AB (intersection_symm AB HK x)
  euclid_finish

end Elements.Book2
