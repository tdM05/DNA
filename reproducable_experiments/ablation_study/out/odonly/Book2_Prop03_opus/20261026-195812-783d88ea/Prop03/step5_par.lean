import SystemE
import Book2.Prop03.step4_aoff_be
import Book2.Prop03.step4_afbe
import Book2.Prop03.step5_anef
import Book2.Prop03.step5_sbeaf
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step5_par (a b c d e f : Point) (AB CD BE DE AF : Line)
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
    formParallelogram b a e f AB DE BE AF := by
  -- a is off BE (reused)
  have step4_aoff_be : ¬a.onLine BE := by euclid_apply (helper_2_3_step4_aoff_be a b c d AB BE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))
  -- AF does not meet BE (reused)
  have step4_afbe : ¬(AF.intersectsLine BE) := by euclid_apply (helper_2_3_step4_afbe a c d CD BE AF (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show ¬a.onLine BE; assumption)))
  -- a ≠ f
  have step5_anef : a ≠ f := by euclid_apply (helper_2_3_step5_anef a b c d e f AB BE DE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  -- b and e are on the same side of AF
  have step5_sbeaf : b.sameSide e AF := by euclid_apply (helper_2_3_step5_sbeaf a b e f AF BE (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬a.onLine BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  unfold formParallelogram
  repeat' apply And.intro
  all_goals (first | assumption | euclid_finish)

end Elements.Book2
