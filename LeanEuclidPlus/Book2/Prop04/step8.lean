import SystemE
import Book1.Prop06.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step8 (a b c d g : Point) (AB CF AD BD : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hassump1 : ¬(CF.intersectsLine AD))
    (hstep7 : ∠ c:g:b = ∠ g:b:c)
    : |(b─c)| = |(c─g)| := by
  have step5_bgd : between b g d := by sorry
  have had : a ≠ d := by euclid_finish
  have hc_ab : c.onLine AB := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have hgb : g ≠ b := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have hc_off_bd : ¬(c.onLine BD) := offLine_of_two_points c b d AB BD hc_ab hb_ab hcb hb_bd hd_bd hd_off_ab
  have ha_off_bd : ¬(a.onLine BD) := offLine_of_two_points a b d AB BD ha_ab hb_ab hab hb_bd hd_bd hd_off_ab
  have hg_off_ab : ¬(g.onLine AB) := offLine_of_two_points g b a BD AB hg_bd hb_bd hgb hb_ab ha_ab ha_off_bd
  have hb_off_cf : ¬(b.onLine CF) := offLine_of_two_points b c g AB CF hb_ab hc_ab hbc hc_cf hg_cf hg_off_ab
  euclid_apply (Elements.Book1.proposition_6 c g b CF BD AB)
  euclid_finish

end Elements.Book2
