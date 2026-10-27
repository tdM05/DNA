import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step5_ss (a b c d e h : Point) (AH BG CD CH : Line)
    (ha_AH : a.onLine AH) (hd_AH : d.onLine AH)
    (he_AH : e.onLine AH) (hh_AH : h.onLine AH)
    (hb_BG : b.onLine BG) (hc_BG : c.onLine BG)
    (hd_CD : d.onLine CD) (hc_CD : c.onLine CD)
    (hh_CH : h.onLine CH) (hc_CH : c.onLine CH)
    (hab_CD : a.sameSide b CD)
    (hpar : ¬AH.intersectsLine BG)
    (hadh : between a d h) (haeh : between a e h) (hdc : d ≠ c) :
    e.sameSide b CH := by
  euclid_finish

end Elements.Book1
