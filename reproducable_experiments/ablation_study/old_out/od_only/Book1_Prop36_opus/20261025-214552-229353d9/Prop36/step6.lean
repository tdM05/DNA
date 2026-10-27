import SystemE

namespace Elements.Book1

theorem helper_1_36_step6 (a b c d e f g h : Point) (AH BG AB CD EF HG BE CH : Line)
    (heAH : e.onLine AH) (hhAH : h.onLine AH) (haAH : a.onLine AH) (hdAH : d.onLine AH)
    (hbBG : b.onLine BG) (hcBG : c.onLine BG) (hfBG : f.onLine BG) (hgBG : g.onLine BG)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hdCD : d.onLine CD) (hcCD : c.onLine CD)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hhHG : h.onLine HG) (hgHG : g.onLine HG)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hdnec : d ≠ c) (hhneg : h ≠ g)
    (hasbCD : a.sameSide b CD) (hesfHG : e.sameSide f HG)
    (hAHBG : ¬(AH.intersectsLine BG)) (hABCD : ¬(AB.intersectsLine CD))
    (hEFHG : ¬(EF.intersectsLine HG))
    (hadh : between a d h) (haeh : between a e h)
    (hbcfg : |(b─c)| = |(f─g)|) (hstep2 : |(b─c)| = |(e─h)|)
    (hstep4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH)
    (hstep5 : |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH)) :
    formParallelogram e h b c AH BG BE CH := by
  euclid_finish

end Elements.Book1
