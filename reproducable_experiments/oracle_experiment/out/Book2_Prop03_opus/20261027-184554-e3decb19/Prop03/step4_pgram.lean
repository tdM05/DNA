import SystemE
import Helpers.Parallel
import Helpers.OffLine
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- The big rectangle AFEB (named by diagonal AE): formParallelogram a b f e AB DE AF BE.
-- Shared by step4 (sum_parallelograms_area) and step5 (rectangle_area).
set_option systemE.solverTime 30 in
theorem helper_2_3_step4_pgram
    (a b c d e f : Point) (AB CD DE BE AF : Line)
    (hc_CD : c.onLine CD) (hc_AB : c.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hbet_acb : between a c b) (hcd_len : |(c─d)| = |(c─b)|) (heb_ne : e ≠ b)
    (hang_bcd : ∠ b:c:d = ∟) (hang_cbe : ∠ c:b:e = ∟) (hdsc_BE : d.sameSide c BE)
    (hd_CD : d.onLine CD) (hf_DE : f.onLine DE) (he_DE : e.onLine DE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF) (hpar_AFCD : ¬AF.intersectsLine CD)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE) (hpar_CDBE : ¬CD.intersectsLine BE)
    (hpar_DEAB : ¬DE.intersectsLine AB) :
    formParallelogram a b f e AB DE AF BE := by
  -- distinctness
  have hcb : c ≠ b := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have hab : a ≠ b := by euclid_finish
  have hcd_ne : c ≠ d := by euclid_finish
  -- off-AB via the two right angles at c and b
  have hd_offAB : ¬d.onLine AB := offLine_of_right_angle c b d AB hc_AB hb_AB hcb hcd_ne hang_bcd
  have he_offAB : ¬e.onLine AB := offLine_of_right_angle b c e AB hb_AB hc_AB hcb.symm heb_ne.symm hang_cbe
  -- off CD / off BE
  have ha_offCD : ¬a.onLine CD := offLine_of_two_points a c d AB CD ha_AB hc_AB hac hc_CD hd_CD hd_offAB
  have ha_offBE : ¬a.onLine BE := offLine_of_two_points a b e AB BE ha_AB hb_AB hab hb_BE he_BE he_offAB
  have hc_offBE : ¬c.onLine BE := by euclid_finish
  -- line distinctness
  have hAFCD : AF ≠ CD := line_ne_of_offLine a AF CD ha_AF ha_offCD
  have hCDBE : CD ≠ BE := line_ne_of_offLine c CD BE hc_CD hc_offBE
  have hAFBE : AF ≠ BE := line_ne_of_offLine a AF BE ha_AF ha_offBE
  -- parallels
  have hAFBE_par : ¬AF.intersectsLine BE :=
    not_intersects_trans AF CD BE hpar_AFCD hpar_CDBE hAFCD hCDBE hAFBE
  have hABDE_par : ¬AB.intersectsLine DE := fun h => hpar_DEAB (intersection_symm AB DE h)
  -- the hard same-side conjunct
  have hss : a.sameSide f BE := sameSide_of_parallel_both a f AF BE ha_AF hf_AF hAFBE hAFBE_par
  exact ⟨ha_AB, hb_AB, hf_DE, he_DE, ha_AF, hf_AF, ⟨hb_BE, he_BE, heb_ne.symm⟩, hss, hABDE_par, hAFBE_par⟩

end Elements.Book2
