import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Parallel
import Mathlib.Tactic.Linarith

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step5 (a b c d e f : Point) (AB CD DE AF BE : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hc_ab : c.onLine AB) (hab : a ≠ b)
    (hbet : between a c b)
    (hd_de : d.onLine DE) (he_de : e.onLine DE)
    (hc_cd : c.onLine CD) (hd_cd : d.onLine CD)
    (ha_af : a.onLine AF) (hf_af : f.onLine AF) (hpar_af : ¬AF.intersectsLine CD)
    (hb_be : b.onLine BE) (he_be : e.onLine BE) (hbe_ne : e ≠ b)
    (hpar_cdbe : ¬CD.intersectsLine BE)
    (hss_dc : d.sameSide c BE) (hpar_deab : ¬DE.intersectsLine AB)
    (hang : ∠ b:c:d = ∟) (hlen : |(c─d)| = |(c─b)|) (hang_bed : ∠ b:e:d = ∟)
    (hstep2 : f.onLine DE ∧ between e d f)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : |(b─e)| = |(c─b)|)   -- "$BE$ (is) equal to $BC$"
    : Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)| := by
  obtain ⟨hf_de, hbet2⟩ := hstep2
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
  have hbeaf : ¬BE.intersectsLine AF := fun h => hafbe (intersection_symm BE AF h)
  have hbe_ss : b.sameSide e AF := sameSide_of_parallel_both b e BE AF hb_be he_be hAFBE.symm hbeaf
  have hDEAB : DE ≠ AB := line_ne_of_offLine d DE AB hd_de hd_nab
  have haf_ne : a ≠ f := by euclid_finish
  have hpara : formParallelogram b a e f AB DE BE AF := by euclid_finish
  have hang_bef : ∠ b:e:f = ∟ := by euclid_finish
  have hrect := rectangle_area b a e f AB DE BE AF ⟨hpara, hang_bef⟩
  obtain ⟨_, hrect2⟩ := hrect
  have hba : |(b─a)| = |(a─b)| := by euclid_finish
  have hbebc : |(b─e)| = |(b─c)| := by euclid_finish
  have haeb : Triangle.area △ a:e:b = Triangle.area △ a:b:e := by euclid_finish
  rw [hba, hbebc] at hrect2
  rw [haeb]
  linarith [hrect2]

end Elements.Book2
