import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step4 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (haAH : a.onLine AH) (hdAH : d.onLine AH) (heAH : e.onLine AH) (hhAH : h.onLine AH)
    (hbBG : b.onLine BG) (hcBG : c.onLine BG)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hpar : ¬AH.intersectsLine BG) (hpar2 : ¬AB.intersectsLine CD)
    (hss : a.sameSide b CD)
    (hadh : between a d h) (haeh : between a e h) :
    distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH := by
  euclid_finish

end Elements.Book1
