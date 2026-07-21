import SystemE

namespace Elements.Book1

theorem helper_1_12_step9 (e g h : Point) (AB : Line)
    (h1 : between e h g) (h2 : e.onLine AB) (h3 : g.onLine AB) :
    h.onLine AB := by
  euclid_finish

end Elements.Book1
