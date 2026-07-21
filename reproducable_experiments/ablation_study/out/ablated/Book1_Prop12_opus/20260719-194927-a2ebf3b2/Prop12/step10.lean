import SystemE

namespace Elements.Book1

theorem helper_1_12_step10 (c e g h : Point) (AB : Line)
    (h1 : ∠ c:h:g = ∠ e:h:c) (h2 : between e h g)
    (h3 : e.onLine AB) (h4 : g.onLine AB) (h5 : ¬(c.onLine AB)) :
    ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟ := by
  euclid_finish

end Elements.Book1
