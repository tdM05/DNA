import SystemE

namespace Elements.Book1

theorem helper_1_47_step3 (a c d f g : Point) (AD FC BC GF AB : Line)
    (h1 : a.onLine AD) (h2 : d.onLine AD) (h3 : f.onLine FC) (h4 : c.onLine FC)
    (h5 : ¬(a.onLine BC)) (h6 : ¬(d.onLine BC)) (h7 : ¬(d.sameSide a BC))
    (h8 : f.onLine GF) (h9 : g.onLine GF) (h10 : ¬(GF.intersectsLine AB))
    (h11 : ¬(g.onLine AB)) (h12 : ¬(g.sameSide c AB)) (h13 : ¬(c.onLine AB)) :
    distinctPointsOnLine a d AD ∧ distinctPointsOnLine f c FC := by
  euclid_finish

end Elements.Book1
