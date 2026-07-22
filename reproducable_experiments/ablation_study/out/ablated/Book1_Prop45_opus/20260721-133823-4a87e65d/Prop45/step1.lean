import SystemE

namespace Elements.Book1

theorem helper_1_45_step1 (a b d : Point) (AB DB AD : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : a.onLine AD) (h5 : d.onLine AD) (h6 : AD ≠ AB)
    (h7 : ¬a.onLine DB) (h8 : b.onLine DB) (h9 : d.onLine DB) :
    distinctPointsOnLine d b DB := by
  euclid_finish

end Elements.Book1
