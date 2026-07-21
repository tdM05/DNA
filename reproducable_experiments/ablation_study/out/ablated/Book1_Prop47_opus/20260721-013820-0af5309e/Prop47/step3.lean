import SystemE

namespace Elements.Book1

theorem helper_1_47_step3 (a b c d f g : Point) (AB AD FC BD BF GF : Line)
    (h1 : a.onLine AD) (h2 : d.onLine AD)
    (h3 : f.onLine FC) (h4 : c.onLine FC)
    (h5 : ¬(a.onLine BD)) (h6 : d.onLine BD)
    (h7 : f.onLine GF) (h8 : g.onLine GF)
    (h9 : ¬(GF.intersectsLine AB))
    (h10 : ¬(g.onLine AB)) (h11 : ¬(c.onLine AB)) (h12 : ¬(g.sameSide c AB)) :
    distinctPointsOnLine a d AD ∧ distinctPointsOnLine f c FC := by
  euclid_finish

end Elements.Book1
