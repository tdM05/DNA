import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

open Elements

theorem h_1_46_s5
    (a b c d e c1 : Point)
    (AB AC AD BE DE : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hc_off : ¬c.onLine AB)
    (hc1_AC : c1.onLine AC) (hbet : between a d c1)
    (ha_AD : a.onLine AD) (hd_AD : d.onLine AD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (hpar_DE_AB : ¬DE.intersectsLine AB) (hpar_BE_AD : ¬BE.intersectsLine AD)
    (s2 : |(a─d)| = |(a─b)|) :
    formParallelogram d e a b DE AB AD BE := by

  have had_ne : a ≠ d := by euclid_finish

  have hd_AC : d.onLine AC := between_same_line_in a d c1 AC ⟨hbet, ha_AC, hc1_AC⟩

  have hAC_eq_AD : AC = AD :=
    two_points_determine_line a d AC AD ⟨⟨ha_AC, hd_AC, had_ne⟩, ha_AD, hd_AD⟩

  have hpar_BE_AC : ¬BE.intersectsLine AC := hAC_eq_AD ▸ hpar_BE_AD

  have hAC_ne_BE : AC ≠ BE := by
    intro h
    have hb_on_AC : b.onLine AC := h ▸ hb_BE
    have hAB_eq_AC : AB = AC :=
      two_points_determine_line a b AB AC ⟨⟨ha_AB, hb_AB, hab⟩, ha_AC, hb_on_AC⟩
    exact hc_off (hAB_eq_AC ▸ hc_AC)

  have hc_off_BE : ¬c.onLine BE := by
    intro h
    exact hpar_BE_AC (intersection_lines_common_point c BE AC ⟨h, hc_AC, hAC_ne_BE.symm⟩)

  have hpar_AD_BE : ¬AD.intersectsLine BE := fun h => hpar_BE_AD (intersection_symm AD BE h)

  have hc_on_AD : c.onLine AD := hAC_eq_AD ▸ hc_AC

  have hss : d.sameSide a BE :=
    sameSide_of_parallel' d a c AD BE hd_AD ha_AD hc_on_AD hc_off_BE hpar_AD_BE

  have hDE_ne_AB : DE ≠ AB := by
    intro h
    have hd_on_AB : d.onLine AB := h ▸ hd_DE
    have hAD_eq_AB : AD = AB :=
      two_points_determine_line a d AD AB ⟨⟨ha_AD, hd_AD, had_ne⟩, ha_AB, hd_on_AB⟩
    exact hc_off (hAD_eq_AB ▸ hc_on_AD)

  have hne_eb : e ≠ b := by
    intro h
    have hb_on_DE : b.onLine DE := h ▸ he_DE
    exact hpar_DE_AB (intersection_lines_common_point b DE AB ⟨hb_on_DE, hb_AB, hDE_ne_AB⟩)
  exact ⟨hd_DE, he_DE, ha_AB, hb_AB, hd_AD, ha_AD,
         ⟨he_BE, hb_BE, hne_eb⟩, hss, hpar_DE_AB, hpar_AD_BE⟩

end Elements.Book1
