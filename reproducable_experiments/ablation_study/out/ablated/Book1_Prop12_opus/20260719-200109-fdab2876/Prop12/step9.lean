import SystemE

namespace Elements.Book1

theorem helper_1_12_step9 (e g h : Point) (AB : Line)
    (he : e.onLine AB) (hg : g.onLine AB) (hehg : between e h g) :
    h.onLine AB := by
  euclid_finish

end Elements.Book1
