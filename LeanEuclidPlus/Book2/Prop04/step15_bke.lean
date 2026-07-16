import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Parallel
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step15_bke (a b c d e g k : Point) (AB CF AD BD BE DE HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hb_be : b.onLine BE) (hk_be : k.onLine BE) (he_be : e.onLine BE)
    (hd_de : d.onLine DE) (he_de : e.onLine DE)
    (hg_hk : g.onLine HK) (hk_hk : k.onLine HK)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hbe_len : |(b─e)| = |(a─b)|) (hde_len : |(d─e)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hDE_AB : ¬(DE.intersectsLine AB))
    (hassump1 : ¬(CF.intersectsLine AD))
    : between b k e := by
  have step5_bgd : between b g d := by sorry
  have had : a ≠ d := by euclid_finish
  have hgd : g ≠ d := by euclid_finish
  have hgb : g ≠ b := by euclid_finish
  have hbe : b ≠ e := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have heb : e ≠ b := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have hAB_ne_DE : AB ≠ DE := (line_ne_of_offLine d DE AB hd_de hd_off_ab).symm
  have hAB_DE : ¬(AB.intersectsLine DE) := fun h => hDE_AB (intersection_symm AB DE h)
  have hb_off_de : ¬(b.onLine DE) := offLine_of_parallel_simple b AB DE hb_ab hAB_ne_DE hAB_DE
  have hd_off_be : ¬(d.onLine BE) := offLine_of_two_points d e b DE BE hd_de he_de hde he_be hb_be hb_off_de
  have he_off_bd : ¬(e.onLine BD) := offLine_of_two_points e b d BE BD he_be hb_be heb hb_bd hd_bd hd_off_be
  have hg_off_de : ¬(g.onLine DE) := offLine_of_two_points g d e BD DE hg_bd hd_bd hgd hd_de he_de he_off_bd
  have ha_off_bd : ¬(a.onLine BD) := offLine_of_two_points a b d AB BD ha_ab hb_ab hab hb_bd hd_bd hd_off_ab
  have hg_off_ab : ¬(g.onLine AB) := offLine_of_two_points g b a BD AB hg_bd hb_bd hgb hb_ab ha_ab ha_off_bd
  have hHK_ne_AB : HK ≠ AB := line_ne_of_offLine g HK AB hg_hk hg_off_ab
  have hb_off_hk : ¬(b.onLine HK) := offLine_of_parallel_simple' b AB HK hb_ab (Ne.symm hHK_ne_AB) hHK_AB
  have hAB_HK : ¬(AB.intersectsLine HK) := fun h => hHK_AB (intersection_symm AB HK h)
  have hHK_ne_DE : HK ≠ DE := line_ne_of_offLine g HK DE hg_hk hg_off_de
  have hDE_HK : ¬(DE.intersectsLine HK) :=
    not_intersects_trans DE AB HK hDE_AB hAB_HK (Ne.symm hAB_ne_DE) (Ne.symm hHK_ne_AB) (Ne.symm hHK_ne_DE)
  have hde_ss : d.sameSide e HK := sameSide_of_parallel_both d e DE HK hd_de he_de (Ne.symm hHK_ne_DE) hDE_HK
  have hbd_opp : ¬(b.sameSide d HK) := not_sameSide_of_between b g d HK hg_hk step5_bgd
  have hbe_opp : ¬(b.sameSide e HK) := by euclid_finish
  have hHK_ne_BE : HK ≠ BE := (line_ne_of_offLine b BE HK hb_be hb_off_hk).symm
  exact between_of_not_sameSide b k e HK BE hHK_ne_BE hk_hk hk_be hb_be he_be
    (by euclid_finish) (by euclid_finish) hbe hbe_opp

end Elements.Book2
