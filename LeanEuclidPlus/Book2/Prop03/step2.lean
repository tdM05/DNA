import SystemE
import Book2.Prop03.step2_efopp
import Book2.Prop03.step2_bet
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step2
    (a b c d e f : Point) (AB CD DE BE AF : Line)
    (hf_DE : f.onLine DE)
    (hd_CD : d.onLine CD) (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hc_CD : c.onLine CD) (hc_AB : c.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hbet_acb : between a c b) (hde_len : |(d─e)| = |(c─b)|) (hcd_len : |(c─d)| = |(c─b)|)
    (hang_bcd : ∠ b:c:d = ∟) (hdsc_BE : d.sameSide c BE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF) (hpar_AFCD : ¬AF.intersectsLine CD)
    (he_BE : e.onLine BE) (hb_BE : b.onLine BE) (hpar_CDBE : ¬CD.intersectsLine BE)
    (hpar_DEAB : ¬DE.intersectsLine AB) :
    f.onLine DE ∧ between e d f := by
  have step2_efopp : ¬(e.sameSide f CD) := by euclid_apply (helper_2_3_step2_efopp a b c d e f AB CD BE AF (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)))
  have step2_bet : between e d f := by euclid_apply (helper_2_3_step2_bet a b c d e f AB CD DE BE AF (by euclid_assumption "" (show ¬(e.sameSide f CD); assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show |(d─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)))
  exact ⟨hf_DE, step2_bet⟩

end Elements.Book2
