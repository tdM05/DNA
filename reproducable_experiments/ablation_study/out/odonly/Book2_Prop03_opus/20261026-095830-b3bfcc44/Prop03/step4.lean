import SystemE
import Book2.Prop03.step4_afbe
import Book2.Prop03.step4_sfbe
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step4 (a b c d e f : Point) (AB CD DE BE AF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD)
    (hdscBE : d.sameSide c BE) (hcbe : ∠ c:b:e = ∟)
    (heb : e ≠ b)
    (hDEAB : ¬DE.intersectsLine AB) (hCDBE : ¬CD.intersectsLine BE)
    (hAFCD : ¬AF.intersectsLine CD)
    (hacb : between a c b)
    (hstep2 : f.onLine DE ∧ between e d f) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b) := by
  obtain ⟨_, hedf⟩ := hstep2
  have step4_afbe : ¬AF.intersectsLine BE := by euclid_apply (helper_2_3_step4_afbe a b c d e AB CD DE BE AF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ∠ c:b:e = ∟; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  have step4_sfbe : a.sameSide f BE := by euclid_apply (helper_2_3_step4_sfbe a b c d e f AB CD DE BE AF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ∠ c:b:e = ∟; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  have hpara : formParallelogram a b f e AB DE AF BE := by euclid_finish
  euclid_apply (sum_parallelograms_area a b f e c d AB DE AF BE)
  euclid_finish

end Elements.Book2
