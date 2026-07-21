import SystemE

namespace Elements.Book1

theorem helper_1_12_step4 (c e g h : Point) (AB CG CH CE : Line)
    (hcCG : c.onLine CG) (hgCG : g.onLine CG)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (he : e.onLine AB) (hg : g.onLine AB) (hc : ¬(c.onLine AB))
    (hehg : between e h g) :
    distinctPointsOnLine c g CG ∧ distinctPointsOnLine c h CH ∧ distinctPointsOnLine c e CE := by
  euclid_finish

end Elements.Book1
