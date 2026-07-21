import SystemE

namespace Elements.Book1

theorem helper_1_36_step1 (a b c d e f g h : Point) (AH BG AB CD EF HG BE CH : Line)
    (h1 : a.onLine AH) (h2 : d.onLine AH) (h3 : e.onLine AH) (h4 : h.onLine AH)
    (h5 : b.onLine BG) (h6 : c.onLine BG) (h7 : f.onLine BG) (h8 : g.onLine BG)
    (h9 : a.onLine AB) (h10 : b.onLine AB) (h11 : d.onLine CD) (h12 : c.onLine CD)
    (h13 : e.onLine EF) (h14 : f.onLine EF) (h15 : h.onLine HG) (h16 : g.onLine HG)
    (h17 : e.onLine BE) (h18 : b.onLine BE) (h19 : h.onLine CH) (h20 : c.onLine CH)
    (h21 : a.sameSide b CD) (h22 : e.sameSide f HG)
    (h23 : ¬(AH.intersectsLine BG)) (h24 : ¬(AB.intersectsLine CD)) (h25 : ¬(EF.intersectsLine HG))
    (h26 : between a d h) (h27 : between a e h)
    (h28 : |(b─c)| = |(f─g)|) :
    distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH := by
  euclid_finish

end Elements.Book1
