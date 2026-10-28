import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
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
  have step2_efopp : ¬(e.sameSide f CD) := by sorry
  have step2_bet : between e d f := by sorry
  exact ⟨hf_DE, step2_bet⟩

end Elements.Book2
