import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop03.step5_afbe
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step5 (a b c d e f : Point) (AB DE CD AF BE : Line)
    (h_acb : between a c b)
    (h_step2 : f.onLine DE ∧ between e d f)
    (hassump1 : |(b─e)| = |(c─b)|)   -- "$BE$ (is) equal to $BC$"
    (h_bed : ∠ b:e:d = ∟)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_c_AB : c.onLine AB)
    (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE) (h_f_DE : f.onLine DE)
    (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD)
    (h_a_AF : a.onLine AF) (h_f_AF : f.onLine AF)
    (h_AF_CD : ¬AF.intersectsLine CD)
    (h_e_BE : e.onLine BE) (h_b_BE : b.onLine BE)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_CD_BE : ¬CD.intersectsLine BE)
    (h_dsc_BE : d.sameSide c BE) (h_eb : e ≠ b) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)| := by
  have step5_afbe : ¬(AF.intersectsLine BE) := by euclid_apply (helper_2_3_step5_afbe a b c d e f AB DE CD AF BE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  have h_par : formParallelogram a b f e AB DE AF BE := by euclid_finish
  have h_par2 : formParallelogram b a e f AB DE BE AF := by euclid_finish
  have h_bef : ∠ b:e:f = ∟ := by euclid_finish
  -- the two diagonal splits of rectangle AFEB are equal (parallelogram_area)
  have hpar : Triangle.area △ a:f:e + Triangle.area △ a:e:b
      = Triangle.area △ b:a:f + Triangle.area △ b:f:e := by
    euclid_apply (parallelogram_area a b f e AB DE AF BE)
    euclid_finish
  -- the BF-diagonal split equals |AB|*|BE| (rectangle_area at vertex B)
  have hrect : Triangle.area △ b:e:f + Triangle.area △ b:a:f = |(b─a)| * |(b─e)| := by
    euclid_apply (rectangle_area b a e f AB DE BE AF)
    euclid_finish
  have hsym : Triangle.area △ b:f:e = Triangle.area △ b:e:f := area_symm_2 b f e
  have h1 : |(b─a)| = |(a─b)| := by euclid_finish
  have h2 : |(b─e)| = |(b─c)| := by euclid_finish
  have hprod : |(b─a)| * |(b─e)| = |(a─b)| * |(b─c)| := by rw [h1, h2]
  linarith [hpar, hrect, hsym, hprod]

end Elements.Book2
