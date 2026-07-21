import SystemE

namespace Elements.Book1

theorem helper_1_12_step11 (a b c e g h : Point) (AB : Line)
    (h1 : ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟)
    (h2 : a.onLine AB) (h3 : b.onLine AB) (h4 : a ≠ b)
    (h5 : g.onLine AB) (h6 : h.onLine AB) (h7 : ¬ c.onLine AB)
    (h8 : between e h g) :
    ∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟ := by
  euclid_finish

end Elements.Book1
