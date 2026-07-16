import SystemE
import Book1.Prop06.Main
import Book1Variants.Prop29
import Helpers.OffLine
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step22_hdhg (a b c d e g h : Point) (AB CF AD BD DE HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD) (hh_ad : h.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hd_de : d.onLine DE) (he_de : e.onLine DE)
    (hg_hk : g.onLine HK) (hh_hk : h.onLine HK)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|) (hde_len : |(d─e)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hDE_AB : ¬(DE.intersectsLine AB))
    (hassump1 : ¬(CF.intersectsLine AD))
    (hstep6 : ∠ a:d:b = ∠ a:b:d)
    : |(h─d)| = |(h─g)| := by
  have step5_bgd : between b g d := by sorry
  have step22_ahd : between a h d := by sorry
  have had : a ≠ d := by euclid_finish
  have hgd : g ≠ d := by euclid_finish
  have hgb : g ≠ b := by euclid_finish
  have hhd : h ≠ d := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have ha_off_bd : ¬(a.onLine BD) := offLine_of_two_points a b d AB BD ha_ab hb_ab hab hb_bd hd_bd hd_off_ab
  have hb_off_ad : ¬(b.onLine AD) := offLine_of_two_points b a d AB AD hb_ab ha_ab (Ne.symm hab) ha_ad hd_ad hd_off_ab
  have hh_off_bd : ¬(h.onLine BD) := offLine_of_two_points h d b AD BD hh_ad hd_ad hhd hd_bd hb_bd hb_off_ad
  have hg_off_ad : ¬(g.onLine AD) := offLine_of_two_points g d a BD AD hg_bd hd_bd hgd hd_ad ha_ad ha_off_bd
  have hg_off_ab : ¬(g.onLine AB) := offLine_of_two_points g b a BD AB hg_bd hb_bd hgb hb_ab ha_ab ha_off_bd
  have hha_ss : h.sameSide a BD := sameSide_of_between d h a BD hd_bd hh_off_bd (by euclid_finish)
  have hae : ∠ h:d:g = ∠ h:g:d := by
    euclid_apply (Elements.Book1.proposition_29'''' h a d g b HK AB BD)
    euclid_finish
  euclid_apply (Elements.Book1.proposition_6 h d g AD BD HK)
  euclid_finish

end Elements.Book2
