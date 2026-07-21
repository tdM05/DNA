import SystemE

namespace Elements.Book1

theorem helper_1_45_step1 (a b d : Point) (AB AD DB : Line)
    (h1 : d.onLine DB) (h2 : b.onLine DB)
    (h3 : a.onLine AB) (h4 : b.onLine AB) (h5 : a ≠ b)
    (h6 : a.onLine AD) (h7 : d.onLine AD) (h8 : AD ≠ AB) :
    distinctPointsOnLine d b DB := by
  euclid_finish

end Elements.Book1
