import SystemE

namespace Elements.Book1

theorem p13tri (a b d : Point) (AB BD AD : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BD) (h5 : d.onLine BD)
    (h6 : a.onLine AD) (h7 : d.onLine AD)
    (h8 : ¬(a.onLine BD)) (h9 : ¬(d.onLine AB)) (h10 : a ≠ d) (h11 : b ≠ d) :
    formTriangle a b d AB BD AD := by
  euclid_finish

end Elements.Book1
