import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step4 (a b c d e h : Point) (AH BG CD BE CH : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hbBG : b.onLine BG) (hcBG : c.onLine BG) (haAH : a.onLine AH) (hdAH : d.onLine AH) (hhAH : h.onLine AH)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD) (hdc : d ≠ c) (hss : a.sameSide b CD)
    (hpar : ¬AH.intersectsLine BG) (hbaeh : between a e h) (hadh : between a d h) :
    distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH := by
  euclid_finish

end Elements.Book1
