import SystemE

namespace Elements.Book1

theorem helper_1_36_step6 (a b c d e f g h : Point) (AH BG AB CD EF HG BE CH : Line)
    (h1 : a.onLine AH) (h2 : d.onLine AH) (h3 : b.onLine BG) (h4 : c.onLine BG)
    (h5 : a.onLine AB) (h6 : b.onLine AB) (h7 : d.onLine CD) (h8 : c.onLine CD)
    (h9 : d ≠ c) (h10 : a.sameSide b CD) (h11 : ¬(AH.intersectsLine BG)) (h12 : ¬(AB.intersectsLine CD))
    (h13 : e.onLine AH) (h14 : h.onLine AH) (h15 : f.onLine BG) (h16 : g.onLine BG)
    (h17 : e.onLine EF) (h18 : f.onLine EF) (h19 : h.onLine HG) (h20 : g.onLine HG)
    (h21 : e.sameSide f HG)
    (h22 : b.onLine BE) (h23 : e.onLine BE) (h24 : c.onLine CH) (h25 : h.onLine CH)
    (h26 : between a d h) (h27 : between a e h)
    (h28 : |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH)) :
    formParallelogram e h b c AH BG BE CH := by
  euclid_finish

end Elements.Book1
