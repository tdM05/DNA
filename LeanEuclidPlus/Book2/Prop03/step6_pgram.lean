import SystemE
import Helpers.OffLine
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- The left rectangle ACDF, labeled so rectangle_area yields |(c─a)| * |(c─d)| (sides c→a and c→d).
theorem helper_2_3_step6_pgram
    (a b c d e f : Point) (AB CD DE AF : Line)
    (hc_CD : c.onLine CD) (hc_AB : c.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hbet_acb : between a c b) (hcd_len : |(c─d)| = |(c─b)|) (hang_bcd : ∠ b:c:d = ∟)
    (hd_CD : d.onLine CD) (hd_DE : d.onLine DE) (hf_DE : f.onLine DE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF) (hpar_AFCD : ¬AF.intersectsLine CD)
    (hpar_DEAB : ¬DE.intersectsLine AB) :
    formParallelogram c a d f AB DE CD AF := by
  have hcb : c ≠ b := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have hcd_ne : c ≠ d := by euclid_finish
  have hd_offAB : ¬d.onLine AB := offLine_of_right_angle c b d AB hc_AB hb_AB hcb hcd_ne hang_bcd
  have ha_offCD : ¬a.onLine CD := offLine_of_two_points a c d AB CD ha_AB hc_AB hac hc_CD hd_CD hd_offAB
  have hAFCD : AF ≠ CD := line_ne_of_offLine a AF CD ha_AF ha_offCD
  have hCDAF_par : ¬CD.intersectsLine AF := fun h => hpar_AFCD (intersection_symm CD AF h)
  have hABDE_par : ¬AB.intersectsLine DE := fun h => hpar_DEAB (intersection_symm AB DE h)
  have hss_cd_af : c.sameSide d AF := sameSide_of_parallel_both c d CD AF hc_CD hd_CD hAFCD.symm hCDAF_par
  have ha_offDE : ¬a.onLine DE :=
    offLine_of_parallel_simple' a AB DE ha_AB (line_ne_of_offLine d DE AB hd_DE hd_offAB).symm hpar_DEAB
  have hafne : a ≠ f := fun h => ha_offDE (h ▸ hf_DE)
  exact ⟨hc_AB, ha_AB, hd_DE, hf_DE, hc_CD, hd_CD, ⟨ha_AF, hf_AF, hafne⟩, hss_cd_af, hABDE_par, hCDAF_par⟩

end Elements.Book2
