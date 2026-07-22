import SystemE
import Helpers.OffLine
import Helpers.SameSide

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step6_para (a b c d f : Point) (AB CD DE AF : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hc_ab : c.onLine AB) (hab : a ≠ b)
    (hbet : between a c b)
    (hd_de : d.onLine DE) (hf_de : f.onLine DE)
    (hc_cd : c.onLine CD) (hd_cd : d.onLine CD)
    (ha_af : a.onLine AF) (hf_af : f.onLine AF) (hpar_af : ¬AF.intersectsLine CD)
    (hpar_deab : ¬DE.intersectsLine AB)
    (hang : ∠ b:c:d = ∟) (hlen : |(c─d)| = |(c─b)|) :
    formParallelogram c a d f AB DE CD AF := by
  have hac : a ≠ c := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have hcd : c ≠ d := by euclid_finish
  have hd_nab : ¬d.onLine AB := offLine_of_right_angle c b d AB hc_ab hb_ab (Ne.symm hbc) hcd hang
  have hna_cd : ¬a.onLine CD := offLine_of_two_points a c d AB CD ha_ab hc_ab hac hc_cd hd_cd hd_nab
  have hAFCD : AF ≠ CD := line_ne_of_offLine a AF CD ha_af hna_cd
  have hcdaf : ¬CD.intersectsLine AF := fun h => hpar_af (intersection_symm CD AF h)
  have hcd_ss : c.sameSide d AF := sameSide_of_parallel_both c d CD AF hc_cd hd_cd hAFCD.symm hcdaf
  have hab_de : ¬AB.intersectsLine DE := fun h => hpar_deab (intersection_symm AB DE h)
  have hDEAB : DE ≠ AB := line_ne_of_offLine d DE AB hd_de hd_nab
  have haf_ne : a ≠ f := by euclid_finish
  exact ⟨hc_ab, ha_ab, hd_de, hf_de, hc_cd, hd_cd, ⟨ha_af, hf_af, haf_ne⟩, hcd_ss, hab_de, hcdaf⟩

end Elements.Book2
