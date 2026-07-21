import SystemE

namespace Elements.Book1

theorem helper_1_36_step1 (a b c d e f g h : Point) (AH BG AB CD EF HG BE CH : Line)
    (p1 : a.onLine AH) (p2 : d.onLine AH) (p3 : e.onLine AH) (p4 : h.onLine AH)
    (p5 : b.onLine BG) (p6 : c.onLine BG) (p7 : f.onLine BG) (p8 : g.onLine BG)
    (p9 : a.onLine AB) (p10 : b.onLine AB) (p11 : d.onLine CD) (p12 : c.onLine CD)
    (p13 : e.onLine EF) (p14 : f.onLine EF) (p15 : h.onLine HG) (p16 : g.onLine HG)
    (p17 : d ≠ c) (p18 : h ≠ g) (p19 : a.sameSide b CD) (p20 : e.sameSide f HG)
    (p21 : ¬(AH.intersectsLine BG)) (p22 : ¬(AB.intersectsLine CD)) (p23 : ¬(EF.intersectsLine HG))
    (p24 : |(b─c)| = |(f─g)|) (p25 : between a d h) (p26 : between a e h)
    (p27 : b.onLine BE) (p28 : e.onLine BE) (p29 : c.onLine CH) (p30 : h.onLine CH) :
    distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH := by
  euclid_finish

end Elements.Book1
