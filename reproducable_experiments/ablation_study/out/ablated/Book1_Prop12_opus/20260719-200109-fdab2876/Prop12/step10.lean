import SystemE

namespace Elements.Book1

theorem helper_1_12_step10 (c e g h : Point) (AB : Line)
    (he : e.onLine AB) (hg : g.onLine AB) (hehg : between e h g)
    (hc : ¬(c.onLine AB)) (hang : ∠ c:h:g = ∠ e:h:c) :
    ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟ := by
  euclid_finish

end Elements.Book1
