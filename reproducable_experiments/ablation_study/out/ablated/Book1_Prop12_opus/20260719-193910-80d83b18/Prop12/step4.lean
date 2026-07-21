import SystemE

namespace Elements.Book1

theorem helper_1_12_step4 (c e g h : Point) (AB CG CH CE : Line)
    (h1 : c.onLine CG) (h2 : g.onLine CG)
    (h3 : c.onLine CH) (h4 : h.onLine CH)
    (h5 : c.onLine CE) (h6 : e.onLine CE)
    (h7 : ¬ c.onLine AB) (h8 : e.onLine AB) (h9 : g.onLine AB)
    (h10 : between e h g) :
    distinctPointsOnLine c g CG ∧ distinctPointsOnLine c h CH ∧ distinctPointsOnLine c e CE := by
  euclid_finish

end Elements.Book1
