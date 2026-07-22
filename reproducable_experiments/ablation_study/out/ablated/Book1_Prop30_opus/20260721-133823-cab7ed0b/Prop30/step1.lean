import SystemE

namespace Elements.Book1

theorem helper_1_30_step1 (a c e g h k : Point) (AB CD EF GK : Line)
    (h1 : g.onLine AB) (h2 : g.onLine GK) (h3 : a.onLine AB)
    (h4 : e.onLine EF) (h5 : e.sameSide a GK)
    (h6 : h.onLine EF) (h7 : h.onLine GK)
    (h8 : k.onLine CD) (h9 : k.onLine GK)
    (h10 : c.onLine CD) (h11 : c.sameSide a GK) :
    AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ CD.intersectsLine GK := by
  euclid_finish

end Elements.Book1
