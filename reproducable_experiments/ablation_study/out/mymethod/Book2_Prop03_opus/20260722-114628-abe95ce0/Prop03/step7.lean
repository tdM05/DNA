import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Mathlib.Tactic.Linarith

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step7 (a b c d e : Point) (AB CD BE DE : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hc_ab : c.onLine AB) (hab : a ≠ b)
    (hbet : between a c b)
    (hc_cd : c.onLine CD) (hd_cd : d.onLine CD)
    (hb_be : b.onLine BE) (he_be : e.onLine BE)
    (hd_de : d.onLine DE) (he_de : e.onLine DE)
    (hpar_cdbe : ¬(CD.intersectsLine BE)) (hpar_deab : ¬(DE.intersectsLine AB))
    (hang : ∠ b:c:d = ∟) (hang_cbe : ∠ c:b:e = ∟)
    (hlen_cd : |(c─d)| = |(c─b)|) (hlen_de : |(d─e)| = |(c─b)|) :
    Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)| := by
  have hbc : b ≠ c := by euclid_finish
  have hcb : c ≠ b := Ne.symm hbc
  have hcd : c ≠ d := by euclid_finish
  have hde_ne : d ≠ e := by euclid_finish
  have hd_nab : ¬d.onLine AB := offLine_of_right_angle c b d AB hc_ab hb_ab hcb hcd hang
  have hAB_ne_DE : AB ≠ DE := (line_ne_of_offLine d DE AB hd_de hd_nab).symm
  have hpar_abde : ¬(AB.intersectsLine DE) := fun h => hpar_deab (intersection_symm AB DE h)
  have hcb_ss : c.sameSide b DE := sameSide_of_parallel_both c b AB DE hc_ab hb_ab hAB_ne_DE hpar_abde
  have hpara : formParallelogram c d b e CD BE AB DE :=
    ⟨hc_cd, hd_cd, hb_be, he_be, hc_ab, hb_ab, ⟨hd_de, he_de, hde_ne⟩, hcb_ss, hpar_cdbe, hpar_abde⟩
  obtain ⟨hrect1, _⟩ := rectangle_area c d b e CD BE AB DE ⟨hpara, hang_cbe⟩
  have hces : Triangle.area △ c:e:b = Triangle.area △ c:b:e := by euclid_finish
  have hcb_len : |(c─b)| = |(b─c)| := by euclid_finish
  rw [hlen_cd] at hrect1
  rw [hcb_len] at hrect1
  rw [hces]
  linarith [hrect1]

end Elements.Book2
