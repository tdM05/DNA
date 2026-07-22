import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step7 (b c d e : Point) (AB DE CD BE : Line)
    (hc_AB : c.onLine AB) (hb_AB : b.onLine AB)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (he_BE : e.onLine BE) (hb_BE : b.onLine BE) (heb_ne : e ≠ b)
    (h_dc_be : d.sameSide c BE) (hcde : ∠ c:d:e = ∟)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE))
    (hcd_eq : |(c─d)| = |(c─b)|) :
    Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)| := by
  have hbe_ne : b ≠ e := heb_ne.symm
  have h_cd_be : c.sameSide d BE := same_side_symm d c BE h_dc_be
  have hABDE : ¬(AB.intersectsLine DE) := fun h => hDEAB (intersection_symm AB DE h)
  have hpar : formParallelogram c b d e AB DE CD BE :=
    ⟨hc_AB, hb_AB, hd_DE, he_DE, hc_CD, hd_CD, ⟨hb_BE, he_BE, hbe_ne⟩, h_cd_be, hABDE, hCDBE⟩
  have hrect := (rectangle_area c b d e AB DE CD BE ⟨hpar, hcde⟩).1
  have hs1 : Triangle.area △ c:b:e = Triangle.area △ c:e:b := area_symm_2 c b e
  have hs2 : |(c─b)| = |(b─c)| := segment_symmetric c b
  have hs3 : |(c─d)| = |(b─c)| := by rw [hcd_eq, hs2]
  rw [hs1] at hrect
  rw [hs2, hs3] at hrect
  linarith [hrect]

end Elements.Book2
