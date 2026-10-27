import SystemE
import Book2.Prop03.step2_hbe
import Book2.Prop03.step7_cnd
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step7_par (a b c d e : Point) (AB CD BE DE : Line)
    (hbetween : between a c b)
    (hc_AB : c.onLine AB) (hb_AB : b.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_CD_BE : ¬CD.intersectsLine BE)
    (hdc_BE : d.sameSide c BE)
    (h_cd_cb : |(c─d)| = |(c─b)|)
    (h_eb : e ≠ b) :
    formParallelogram b c e d AB DE BE CD := by
  -- b and e on the same side of CD (reused)
  have step2_hbe : b.sameSide e CD := by euclid_apply (helper_2_3_step2_hbe b c d e CD BE (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  -- c ≠ d (|c─d| = |c─b| and c ≠ b)
  have step7_cnd : c ≠ d := by euclid_apply (helper_2_3_step7_cnd a b c d (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)))
  unfold formParallelogram
  repeat' apply And.intro
  all_goals (first | assumption | euclid_finish)

end Elements.Book2
