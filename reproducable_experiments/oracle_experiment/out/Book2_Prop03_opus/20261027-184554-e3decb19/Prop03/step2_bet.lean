import SystemE
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_3_step2_bet
    (a b c d e f : Point) (AB CD DE BE AF : Line)
    (hef_opp : ¬(e.sameSide f CD))
    (hd_CD : d.onLine CD) (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hf_DE : f.onLine DE)
    (hc_CD : c.onLine CD) (hc_AB : c.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hbet_acb : between a c b) (hde_len : |(d─e)| = |(c─b)|) (hcd_len : |(c─d)| = |(c─b)|)
    (hang_bcd : ∠ b:c:d = ∟) (hdsc_BE : d.sameSide c BE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF) (hpar_AFCD : ¬AF.intersectsLine CD)
    (he_BE : e.onLine BE) (hb_BE : b.onLine BE) (hpar_CDBE : ¬CD.intersectsLine BE)
    (hpar_DEAB : ¬DE.intersectsLine AB) :
    between e d f := by
  have hCDDE : CD ≠ DE := by euclid_finish
  have hed : e ≠ d := by euclid_finish
  have hfd : f ≠ d := by euclid_finish
  have hef : e ≠ f := by euclid_finish
  exact between_of_not_sameSide e d f CD DE hCDDE hd_CD hd_DE he_DE hf_DE hed hfd hef hef_opp

end Elements.Book2
