import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Parallel
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step22_dfe (a b c d e f g : Point) (AB CF AD BD BE DE : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF) (hf_cf : f.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_be : b.onLine BE) (he_be : e.onLine BE)
    (hd_de : d.onLine DE) (he_de : e.onLine DE) (hf_de : f.onLine DE)
    (hang : ∠ b:a:d = ∟) (hang_e : ∠ a:b:e = ∟)
    (had_len : |(a─d)| = |(a─b)|) (hbe_len : |(b─e)| = |(a─b)|) (hde_len : |(d─e)| = |(a─b)|)
    (hassump1 : ¬(CF.intersectsLine AD)) (hCF_BE : ¬(CF.intersectsLine BE))
    (hDE_AB : ¬(DE.intersectsLine AB))
    : between d f e := by
  have had : a ≠ d := by euclid_finish
  have hbe : b ≠ e := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have he_off_ab : ¬(e.onLine AB) := offLine_of_right_angle b a e AB hb_ab ha_ab (Ne.symm hab) hbe hang_e
  have hc_ab : c.onLine AB := by euclid_finish
  have hca : c ≠ a := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hc_off_ad : ¬(c.onLine AD) := offLine_of_two_points c a d AB AD hc_ab ha_ab hca ha_ad hd_ad hd_off_ab
  have hAD_ne_CF : AD ≠ CF := line_ne_of_offLine c CF AD hc_cf hc_off_ad |>.symm
  have hAD_CF : ¬(AD.intersectsLine CF) := fun x => hassump1 (intersection_symm AD CF x)
  have had_ss : a.sameSide d CF := sameSide_of_parallel_both a d AD CF ha_ad hd_ad hAD_ne_CF hAD_CF
  -- b, e same side of CF (BE ∥ CF)
  have hc_off_be : ¬(c.onLine BE) := offLine_of_two_points c b e AB BE hc_ab hb_ab hcb hb_be he_be he_off_ab
  have hBE_ne_CF : BE ≠ CF := (line_ne_of_offLine c CF BE hc_cf hc_off_be).symm
  have hBE_CF : ¬(BE.intersectsLine CF) := fun x => hCF_BE (intersection_symm BE CF x)
  have hbe_ss : b.sameSide e CF := sameSide_of_parallel_both b e BE CF hb_be he_be hBE_ne_CF hBE_CF
  -- a, b opposite across CF
  have hab_opp : ¬(a.sameSide b CF) := not_sameSide_of_between a c b CF hc_cf hacb
  have hde_opp : ¬(d.sameSide e CF) := by euclid_finish
  -- f is between d and e
  have hAB_ne_DE : AB ≠ DE := (line_ne_of_offLine d DE AB hd_de hd_off_ab).symm
  have hc_off_de : ¬(c.onLine DE) := offLine_of_parallel_simple' c AB DE hc_ab hAB_ne_DE hDE_AB
  have hCF_ne_DE : CF ≠ DE := line_ne_of_offLine c CF DE hc_cf hc_off_de
  exact between_of_not_sameSide d f e CF DE hCF_ne_DE hf_cf hf_de hd_de he_de
    (by euclid_finish) (by euclid_finish) hde hde_opp

end Elements.Book2
