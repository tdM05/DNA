import SystemE
import Helpers.Pasch
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step5_bgd (a b c d g : Point) (AB CF AD BD : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hassump1 : ¬(CF.intersectsLine AD))
    : between b g d := by
  have hc_ab : c.onLine AB := by euclid_finish
  have hca : c ≠ a := by euclid_finish
  have had : a ≠ d := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have hc_off_ad : ¬(c.onLine AD) := offLine_of_two_points c a d AB AD hc_ab ha_ab hca ha_ad hd_ad hd_off_ab
  have hd_off_cf : ¬(d.onLine CF) := offLine_of_parallel d c AD CF hd_ad hc_cf hc_off_ad hassump1
  have hAD_ne_CF : AD ≠ CF := line_ne_of_offLine d AD CF hd_ad hd_off_cf
  have hpar' : ¬(AD.intersectsLine CF) := fun h => hassump1 (intersection_symm AD CF h)
  have h_ad_same : a.sameSide d CF := sameSide_of_parallel_both a d AD CF ha_ad hd_ad hAD_ne_CF hpar'
  have h_ab_opp : ¬(a.sameSide b CF) := not_sameSide_of_between a c b CF hc_cf hacb
  have h_bd_opp : ¬(b.sameSide d CF) := by euclid_finish
  have hCF_ne_BD : CF ≠ BD := (line_ne_of_offLine d BD CF hd_bd hd_off_cf).symm
  exact between_of_not_sameSide b g d CF BD hCF_ne_BD hg_cf hg_bd hb_bd hd_bd
    (by euclid_finish) (by euclid_finish) hbd h_bd_opp

end Elements.Book2
