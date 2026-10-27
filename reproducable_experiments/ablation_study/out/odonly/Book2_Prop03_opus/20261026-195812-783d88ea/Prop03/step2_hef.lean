import SystemE
import Book2.Prop03.step2_hab
import Book2.Prop03.step2_hbe
import Book2.Prop03.step2_haf
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step2_hef (a b c d e f : Point) (AB CD BE DE AF : Line)
    (hbetween : between a c b)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hf_DE : f.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
    (h_CD_BE : ¬CD.intersectsLine BE)
    (h_AF_CD : ¬AF.intersectsLine CD)
    (hdc_BE : d.sameSide c BE)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_ab : a ≠ b) (h_eb : e ≠ b) :
    ¬(e.sameSide f CD) := by
  -- a and b are on opposite sides of CD (CD crosses AB at c, with between a c b)
  have step2_hab : ¬(a.sameSide b CD) := by euclid_apply (helper_2_3_step2_hab a b c CD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)))
  -- b and e on the same side of CD (BE is parallel to CD)
  have step2_hbe : b.sameSide e CD := by euclid_apply (helper_2_3_step2_hbe b c d e CD BE (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  -- a and f on the same side of CD (AF is parallel to CD)
  have step2_haf : a.sameSide f CD := by euclid_apply (helper_2_3_step2_haf a b c d e f AB CD BE DE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))
  -- hence e and f are on opposite sides of CD
  euclid_finish

end Elements.Book2
