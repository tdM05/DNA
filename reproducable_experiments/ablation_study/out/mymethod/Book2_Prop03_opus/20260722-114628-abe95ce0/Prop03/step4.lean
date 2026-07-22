import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Parallel

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step4 (a b c d e f : Point) (AB CD DE AF BE : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hc_ab : c.onLine AB) (hab : a ≠ b)
    (hbet : between a c b)
    (hd_de : d.onLine DE) (he_de : e.onLine DE) (hf_de : f.onLine DE)
    (hc_cd : c.onLine CD) (hd_cd : d.onLine CD)
    (ha_af : a.onLine AF) (hf_af : f.onLine AF) (hpar_af : ¬AF.intersectsLine CD)
    (hb_be : b.onLine BE) (he_be : e.onLine BE) (hbe_ne : e ≠ b)
    (hpar_cdbe : ¬CD.intersectsLine BE)
    (hss_dc : d.sameSide c BE) (hpar_deab : ¬DE.intersectsLine AB)
    (hang : ∠ b:c:d = ∟) (hlen : |(c─d)| = |(c─b)|)
    (hstep2 : f.onLine DE ∧ between e d f) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b) := by
  obtain ⟨_, hbet2⟩ := hstep2
  have hac : a ≠ c := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have hcd : c ≠ d := by euclid_finish
  have hd_nab : ¬d.onLine AB := offLine_of_right_angle c b d AB hc_ab hb_ab (Ne.symm hbc) hcd hang
  have hna_cd : ¬a.onLine CD := offLine_of_two_points a c d AB CD ha_ab hc_ab hac hc_cd hd_cd hd_nab
  have hnb_cd : ¬b.onLine CD := offLine_of_two_points b c d AB CD hb_ab hc_ab hbc hc_cd hd_cd hd_nab
  have hAFCD : AF ≠ CD := line_ne_of_offLine a AF CD ha_af hna_cd
  have hCDBE : CD ≠ BE := (line_ne_of_offLine b BE CD hb_be hnb_cd).symm
  have hc_nbe : ¬c.onLine BE := by euclid_finish
  have ha_nbe : ¬a.onLine BE := by euclid_finish
  have hAFBE : AF ≠ BE := line_ne_of_offLine a AF BE ha_af ha_nbe
  have hafbe : ¬AF.intersectsLine BE := not_intersects_trans AF CD BE hpar_af hpar_cdbe hAFCD hCDBE hAFBE
  have haf_ss : a.sameSide f BE := sameSide_of_parallel_both a f AF BE ha_af hf_af hAFBE hafbe
  have hpara : formParallelogram a b f e AB DE AF BE := by euclid_finish
  euclid_apply (sum_parallelograms_area a b f e c d AB DE AF BE)
  euclid_finish

end Elements.Book2
