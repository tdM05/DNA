import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step1 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (hc_CH : c.onLine CH) (hh_CH : h.onLine CH)
    (ha_AH : a.onLine AH) (hd_AH : d.onLine AH)
    (he_AH : e.onLine AH) (hh_AH : h.onLine AH)
    (hb_BG : b.onLine BG) (hc_BG : c.onLine BG)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hd_CD : d.onLine CD) (hc_CD : c.onLine CD) (hdc : d ≠ c)
    (hab_ss : a.sameSide b CD)
    (hpar1 : ¬AB.intersectsLine CD) (hpar : ¬AH.intersectsLine BG) :
    distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH := by
  euclid_finish

end Elements.Book1
