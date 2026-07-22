import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step2 (a b c d e f : Point) (AB CD DE AF BE : Line)
    (hf_de : f.onLine DE) (hd_de : d.onLine DE) (he_de : e.onLine DE)
    (hd_cd : d.onLine CD) (hc_cd : c.onLine CD)
    (ha_af : a.onLine AF) (hf_af : f.onLine AF) (hpar_af : ¬AF.intersectsLine CD)
    (he_be : e.onLine BE) (hb_be : b.onLine BE) (hpar_cdbe : ¬CD.intersectsLine BE)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hc_ab : c.onLine AB)
    (hang : ∠ b:c:d = ∟) (hlen : |(c─d)| = |(c─b)|)
    (hbet : between a c b) :
    f.onLine DE ∧ between e d f := by
  refine ⟨hf_de, ?_⟩
  have hac : a ≠ c := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have hcd : c ≠ d := by euclid_finish
  have hd_nab : ¬d.onLine AB := offLine_of_right_angle c b d AB hc_ab hb_ab (Ne.symm hbc) hcd hang
  have hna_cd : ¬a.onLine CD := offLine_of_two_points a c d AB CD ha_ab hc_ab hac hc_cd hd_cd hd_nab
  have hnb_cd : ¬b.onLine CD := offLine_of_two_points b c d AB CD hb_ab hc_ab hbc hc_cd hd_cd hd_nab
  have hAFCD : AF ≠ CD := line_ne_of_offLine a AF CD ha_af hna_cd
  have hBECD : BE ≠ CD := line_ne_of_offLine b BE CD hb_be hnb_cd
  have hpar_becd : ¬BE.intersectsLine CD := fun h => hpar_cdbe (intersection_symm BE CD h)
  have haf_ss : a.sameSide f CD := sameSide_of_parallel_both a f AF CD ha_af hf_af hAFCD hpar_af
  have hbe_ss : b.sameSide e CD := sameSide_of_parallel_both b e BE CD hb_be he_be hBECD hpar_becd
  have hab_opp : ¬a.sameSide b CD := not_sameSide_of_between a c b CD hc_cd hbet
  have hef_opp : ¬e.sameSide f CD := by euclid_finish
  euclid_finish

end Elements.Book2
