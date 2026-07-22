import SystemE
import Book2.Prop03.step4_afbe
import Book2.Prop03.step4_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step4 (a b c d e f : Point) (AB CD DE AF BE : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
    (hf_DE : f.onLine DE) (he_DE : e.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE) (heb_ne : e ≠ b)
    (hacb : between a c b) (hstep2 : f.onLine DE ∧ between e d f)
    (hbcd : ∠ b:c:d = ∟) (hcbe : ∠ c:b:e = ∟) (h_dc_be : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hAFCD : ¬(AF.intersectsLine CD))
    (hCDBE : ¬(CD.intersectsLine BE)) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b) := by
  obtain ⟨_, hedf⟩ := hstep2
  have step4_afbe : ¬(AF.intersectsLine BE) := by euclid_apply (helper_2_3_step4_afbe a b c d e AB CD BE AF (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ c:b:e = ∟; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine CD); assumption)) (by euclid_assumption "" (show ¬(CD.intersectsLine BE); assumption)))
  have step4_ss : a.sameSide f BE := by euclid_apply (helper_2_3_step4_ss a b c d e f AB CD BE AF (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ c:b:e = ∟; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine BE); assumption)))
  have hABDE : ¬(AB.intersectsLine DE) := fun h => hDEAB (intersection_symm AB DE h)
  have step4_par : formParallelogram a b f e AB DE AF BE :=
    ⟨ha_AB, hb_AB, hf_DE, he_DE, ha_AF, hf_AF, ⟨hb_BE, he_BE, heb_ne.symm⟩, step4_ss, hABDE, step4_afbe⟩
  euclid_apply (sum_parallelograms_area a b f e c d AB DE AF BE)
  euclid_finish

end Elements.Book2
