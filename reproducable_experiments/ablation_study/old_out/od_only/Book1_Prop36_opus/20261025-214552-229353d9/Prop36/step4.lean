import SystemE

namespace Elements.Book1

theorem helper_1_36_step4 (a b c d e h : Point) (AH BG CD BE CH : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (heAH : e.onLine AH) (hhAH : h.onLine AH) (haAH : a.onLine AH) (hdAH : d.onLine AH)
    (hbBG : b.onLine BG) (hcBG : c.onLine BG)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hdnec : d ≠ c)
    (hasbCD : a.sameSide b CD) (hpar : ¬(AH.intersectsLine BG)) :
    distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH := by
  euclid_finish

end Elements.Book1
