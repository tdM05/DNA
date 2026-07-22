import SystemE

namespace Elements.Book1

theorem helper_1_36_step1 (a b c d e h : Point) (AH BG BE CH : Line)
    (h1 : b.onLine BE) (h2 : e.onLine BE) (h3 : c.onLine CH) (h4 : h.onLine CH)
    (h5 : b.onLine BG) (h6 : c.onLine BG) (h7 : e.onLine AH) (h8 : h.onLine AH)
    (h9 : a.onLine AH) (h10 : d.onLine AH) (h11 : ¬(AH.intersectsLine BG))
    (h12 : between a d h) (h13 : between a e h) :
    distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH := by
  euclid_finish

end Elements.Book1
