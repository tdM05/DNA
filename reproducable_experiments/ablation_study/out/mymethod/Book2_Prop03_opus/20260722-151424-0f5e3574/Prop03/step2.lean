import SystemE
import Book2.Prop03.step2_ns
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step2 (a b c d e f : Point) (AB CD BE DE AF : Line)
    (hf_DE : f.onLine DE) (hd_CD : d.onLine CD) (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (he_BE : e.onLine BE) (hb_BE : b.onLine BE) (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
    (hc_CD : c.onLine CD) (hc_AB : c.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hacb : between a c b) (hbcd : ∠ b:c:d = ∟) (h_dc_be : d.sameSide c BE)
    (hCDBE : ¬CD.intersectsLine BE) (hAFCD : ¬AF.intersectsLine CD) :
    f.onLine DE ∧ between e d f := by
  have step2_ns : ¬(e.sameSide f CD) := by euclid_apply (helper_2_3_step2_ns a b c d e f AB CD BE AF (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)))
  refine ⟨hf_DE, ?_⟩
  euclid_apply (pasch_4 e d f CD DE)
  euclid_finish

end Elements.Book2
