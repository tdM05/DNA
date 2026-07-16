import SystemE
import Book1Variants.Prop34
import Book1Variants.Prop29
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Parallel
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step22_ra (a b c d e f g h : Point) (AB CF AD BD BE DE HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF) (hf_cf : f.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD) (hh_ad : h.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hb_be : b.onLine BE) (he_be : e.onLine BE)
    (hd_de : d.onLine DE) (he_de : e.onLine DE) (hf_de : f.onLine DE)
    (hg_hk : g.onLine HK) (hh_hk : h.onLine HK)
    (hang : ∠ b:a:d = ∟) (hang_e : ∠ a:b:e = ∟) (hang_de : ∠ a:d:e = ∟)
    (had_len : |(a─d)| = |(a─b)|) (hbe_len : |(b─e)| = |(a─b)|) (hde_len : |(d─e)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hDE_AB : ¬(DE.intersectsLine AB))
    (hassump1 : ¬(CF.intersectsLine AD)) (hCF_BE : ¬(CF.intersectsLine BE))
    : (∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟) := by
  have step22_par : formParallelogram h g d f HK DE AD CF := by sorry
  have step22_ahd : between a h d := by sorry
  have step22_dfe : between d f e := by sorry
  have had : a ≠ d := by euclid_finish
  have hgd : g ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have hg_off_ab : ¬(g.onLine AB) := by
    have ha_off_bd : ¬(a.onLine BD) := offLine_of_two_points a b d AB BD ha_ab hb_ab hab hb_bd hd_bd hd_off_ab
    have hgb : g ≠ b := by euclid_finish
    exact offLine_of_two_points g b a BD AB hg_bd hb_bd hgb hb_ab ha_ab ha_off_bd
  have hHK_ne_AB : HK ≠ AB := line_ne_of_offLine g HK AB hg_hk hg_off_ab
  have hAB_ne_DE : AB ≠ DE := (line_ne_of_offLine d DE AB hd_de hd_off_ab).symm
  have hAB_HK : ¬(AB.intersectsLine HK) := fun x => hHK_AB (intersection_symm AB HK x)
  have hAB_DE : ¬(AB.intersectsLine DE) := fun x => hDE_AB (intersection_symm AB DE x)
  have hb_off_de : ¬(b.onLine DE) := offLine_of_parallel_simple b AB DE hb_ab hAB_ne_DE hAB_DE
  have he_off_bd : ¬(e.onLine BD) := offLine_of_two_points e d b DE BD he_de hd_de (Ne.symm hde) hd_bd hb_bd hb_off_de
  have hg_off_de : ¬(g.onLine DE) := offLine_of_two_points g d e BD DE hg_bd hd_bd hgd hd_de he_de he_off_bd
  have hHK_ne_DE : HK ≠ DE := line_ne_of_offLine g HK DE hg_hk hg_off_de
  have hHK_DE : ¬(HK.intersectsLine DE) :=
    not_intersects_trans HK AB DE hHK_AB hAB_DE hHK_ne_AB hAB_ne_DE hHK_ne_DE
  have hDE_HK : ¬(DE.intersectsLine HK) := fun x => hHK_DE (intersection_symm DE HK x)
  have hdf_ss : d.sameSide f HK := sameSide_of_parallel_both d f DE HK hd_de hf_de (Ne.symm hHK_ne_DE) hDE_HK
  have hfdh : ∠ f:d:h = ∟ := by euclid_finish
  have hAD_CF : ¬(AD.intersectsLine CF) := fun x => hassump1 (intersection_symm AD CF x)
  euclid_apply (Elements.Book1.proposition_34' h g d f HK DE AD CF)
  euclid_apply (Elements.Book1.proposition_29''''' d f h g AD CF HK)
  euclid_finish

end Elements.Book2
