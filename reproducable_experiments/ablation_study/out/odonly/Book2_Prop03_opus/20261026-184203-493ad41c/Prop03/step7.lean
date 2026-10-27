import SystemE
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step7 (b c d e : Point) (AB DE CD BE : Line)
    (h_cde : ∠ c:d:e = ∟)
    (h_cd : |(c─d)| = |(c─b)|)
    (h_c_AB : c.onLine AB) (h_b_AB : b.onLine AB)
    (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE)
    (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD)
    (h_e_BE : e.onLine BE) (h_b_BE : b.onLine BE)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_CD_BE : ¬CD.intersectsLine BE)
    (h_dsc_BE : d.sameSide c BE) (h_eb : e ≠ b) :
    Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)| := by
  have h_par : formParallelogram c b d e AB DE CD BE := by euclid_finish
  -- rectangle_area at vertex C: the C-E diagonal split equals |CB|*|CD|
  have hrect : Triangle.area △ c:d:e + Triangle.area △ c:b:e = |(c─b)| * |(c─d)| := by
    euclid_apply (rectangle_area c b d e AB DE CD BE)
    euclid_finish
  have hsym : Triangle.area △ c:b:e = Triangle.area △ c:e:b := area_symm_2 c b e
  have h_cb : |(c─b)| = |(b─c)| := by euclid_finish
  have hprod : |(c─b)| * |(c─d)| = |(b─c)| * |(b─c)| := by rw [h_cd, h_cb]
  linarith [hrect, hsym, hprod]

end Elements.Book2
