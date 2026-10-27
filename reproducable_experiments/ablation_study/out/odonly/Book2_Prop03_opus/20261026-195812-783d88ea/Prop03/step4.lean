import SystemE
import Book2.Prop03.step4_par
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step4 (a b c d e f : Point) (AB CD BE DE AF : Line)
    (hbetween : between a c b)
    (hstep2 : f.onLine DE ∧ between e d f)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hf_DE : f.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_AF_CD : ¬AF.intersectsLine CD)
    (h_CD_BE : ¬CD.intersectsLine BE)
    (hdc_BE : d.sameSide c BE)
    (h_eb : e ≠ b) (h_ab : a ≠ b) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b) := by
  -- the big rectangle AFEB is a parallelogram, divided by CD at c (top) and d (bottom)
  have step4_par : formParallelogram a b f e AB DE AF BE := by euclid_apply (helper_2_3_step4_par a b c d e f AB CD BE DE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show f.onLine DE ∧ between e d f; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))
  -- split it by sum_parallelograms_area with division points c (between a b) and d (between f e)
  euclid_apply (sum_parallelograms_area a b f e c d AB DE AF BE)
  euclid_finish

end Elements.Book2
