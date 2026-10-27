import SystemE
import Book2.Prop03.step4_aoff_be
import Book2.Prop03.step4_foff_be
import Book2.Prop03.step4_afbe
import Book2.Prop03.step4_safbe
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step4_par (a b c d e f : Point) (AB CD BE DE AF : Line)
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
    formParallelogram a b f e AB DE AF BE := by
  -- a is off BE (else a,b on BE∩AB ⟹ BE = AB ⟹ c ∈ BE, contra d.sameSide c BE)
  have step4_aoff_be : ¬a.onLine BE := by euclid_apply (helper_2_3_step4_aoff_be a b c d AB BE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))
  -- f is off BE (f ∈ DE, DE ≠ BE, so f ∈ DE∩BE ⟹ f = e, but e ≠ f by between e d f)
  have step4_foff_be : ¬f.onLine BE := by euclid_apply (helper_2_3_step4_foff_be c d e f BE DE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show f.onLine DE ∧ between e d f; assumption)))
  -- AF does not meet BE (both parallel to CD)
  have step4_afbe : ¬(AF.intersectsLine BE) := by euclid_apply (helper_2_3_step4_afbe a c d CD BE AF (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show ¬a.onLine BE; assumption)))
  -- a and f are on the same side of BE (both on AF, which is parallel to BE)
  have step4_safbe : a.sameSide f BE := by euclid_apply (helper_2_3_step4_safbe a f BE AF (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬a.onLine BE; assumption)) (by euclid_assumption "" (show ¬f.onLine BE; assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine BE); assumption)))
  unfold formParallelogram
  repeat' apply And.intro
  all_goals (first | assumption | euclid_finish)

end Elements.Book2
