import SystemE
import Book1Variants.Prop29
import Helpers.OffLine
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step14 (a b c d g k : Point) (AB CF AD BD BE HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hb_be : b.onLine BE) (hk_be : k.onLine BE)
    (hg_hk : g.onLine HK) (hk_hk : k.onLine HK)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hCF_AD : ¬(CF.intersectsLine AD))
    (hassump1 : ¬(CF.intersectsLine BE))   -- "$CG$ is parallel to $BK$"
    : ∠ k:b:c + ∠ g:c:b = ∟ + ∟ := by
  have step5_bgd : between b g d := by sorry
  have had : a ≠ d := by euclid_finish
  have hgb : g ≠ b := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have ha_off_bd : ¬(a.onLine BD) := offLine_of_two_points a b d AB BD ha_ab hb_ab hab hb_bd hd_bd hd_off_ab
  have hg_off_ab : ¬(g.onLine AB) := offLine_of_two_points g b a BD AB hg_bd hb_bd hgb hb_ab ha_ab ha_off_bd
  have hHK_ne_AB : HK ≠ AB := line_ne_of_offLine g HK AB hg_hk hg_off_ab
  have hgk_ss : g.sameSide k AB := sameSide_of_parallel_both g k HK AB hg_hk hk_hk hHK_ne_AB hHK_AB
  euclid_apply (Elements.Book1.proposition_29''''' g k c b CF BE AB)
  euclid_finish

end Elements.Book2
