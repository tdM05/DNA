import SystemE
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step6 (a b c d e f : Point) (AB DE CD AF BE : Line)
    (h_acb : between a c b)
    (h_step2 : f.onLine DE ∧ between e d f)
    (hassump1 : |(c─d)| = |(c─b)|)   -- "$DC$ (is) equal to $CB$"
    (h_cde : ∠ c:d:e = ∟)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_c_AB : c.onLine AB)
    (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE) (h_f_DE : f.onLine DE)
    (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD)
    (h_a_AF : a.onLine AF) (h_f_AF : f.onLine AF)
    (h_AF_CD : ¬AF.intersectsLine CD)
    (h_DE_AB : ¬DE.intersectsLine AB) :
    Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)| := by
  have h_par : formParallelogram a c f d AB DE AF CD := by euclid_finish
  have h_par2 : formParallelogram c a d f AB DE CD AF := by euclid_finish
  have h_cdf : ∠ c:d:f = ∟ := by euclid_finish
  -- the two diagonal splits of rectangle AFDC are equal (parallelogram_area)
  have hpar : Triangle.area △ a:f:d + Triangle.area △ a:d:c
      = Triangle.area △ c:a:f + Triangle.area △ c:f:d := by
    euclid_apply (parallelogram_area a c f d AB DE AF CD)
    euclid_finish
  -- the CF-diagonal split equals |CA|*|CD| (rectangle_area at vertex C)
  have hrect : Triangle.area △ c:d:f + Triangle.area △ c:a:f = |(c─a)| * |(c─d)| := by
    euclid_apply (rectangle_area c a d f AB DE CD AF)
    euclid_finish
  have hsym : Triangle.area △ c:f:d = Triangle.area △ c:d:f := area_symm_2 c f d
  have h1 : |(c─a)| = |(a─c)| := by euclid_finish
  have hprod : |(c─a)| * |(c─d)| = |(a─c)| * |(c─b)| := by rw [h1, hassump1]
  linarith [hpar, hrect, hsym, hprod]

end Elements.Book2
