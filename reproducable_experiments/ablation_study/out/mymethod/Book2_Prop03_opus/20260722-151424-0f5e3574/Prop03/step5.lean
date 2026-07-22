import SystemE
import Helpers.SameSide
import Helpers.OffLine
import Helpers.Parallel
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step5 (a b c d e f : Point) (AB CD DE BE AF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hf_DE : f.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
    (hacb : between a c b) (heb_ne : e ≠ b)
    (hbed : ∠ b:e:d = ∟) (hbcd : ∠ b:c:d = ∟) (hcbe : ∠ c:b:e = ∟)
    (h_dc_be : d.sameSide c BE) (hstep2 : f.onLine DE ∧ between e d f)
    (hAFCD : ¬(AF.intersectsLine CD)) (hCDBE : ¬(CD.intersectsLine BE))
    (hDEAB : ¬(DE.intersectsLine AB))
    (hbe_eq : |(b─e)| = |(c─b)|) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)| := by
  obtain ⟨_, hedf⟩ := hstep2
  have ha_notCD : ¬(a.onLine CD) := by euclid_finish
  have ha_notBE : ¬(a.onLine BE) := by euclid_finish
  have hc_notBE : ¬(c.onLine BE) := by euclid_finish
  have hne_AFCD : AF ≠ CD := line_ne_of_offLine a AF CD ha_AF ha_notCD
  have hne_CDBE : CD ≠ BE := line_ne_of_offLine c CD BE hc_CD hc_notBE
  have hne_AFBE : AF ≠ BE := line_ne_of_offLine a AF BE ha_AF ha_notBE
  have hAFBE : ¬(AF.intersectsLine BE) :=
    not_intersects_trans AF CD BE hAFCD hCDBE hne_AFCD hne_CDBE hne_AFBE
  have hBEAF : ¬(BE.intersectsLine AF) := fun h => hAFBE (intersection_symm BE AF h)
  have hne_BEAF : BE ≠ AF := hne_AFBE.symm
  have h_ss : b.sameSide e AF :=
    sameSide_of_parallel_both b e BE AF hb_BE he_BE hne_BEAF hBEAF
  have hf_notAB : ¬(f.onLine AB) := by euclid_finish
  have haf_ne : a ≠ f := fun h => hf_notAB (h ▸ ha_AB)
  have hABDE : ¬(AB.intersectsLine DE) := fun h => hDEAB (intersection_symm AB DE h)
  have hpar : formParallelogram b a e f AB DE BE AF :=
    ⟨hb_AB, ha_AB, he_DE, hf_DE, hb_BE, he_BE, ⟨ha_AF, hf_AF, haf_ne⟩, h_ss, hABDE, hBEAF⟩
  have hrangle : ∠ b:e:f = ∟ := by euclid_finish
  have hrect := (rectangle_area b a e f AB DE BE AF ⟨hpar, hrangle⟩).2
  have hs1 : Triangle.area △ a:e:b = Triangle.area △ a:b:e := area_symm_2 a e b
  have hs2 : |(b─a)| = |(a─b)| := by euclid_finish
  have hs3 : |(b─e)| = |(b─c)| := by euclid_finish
  rw [hs2, hs3] at hrect
  rw [hs1]
  linarith [hrect]

end Elements.Book2
