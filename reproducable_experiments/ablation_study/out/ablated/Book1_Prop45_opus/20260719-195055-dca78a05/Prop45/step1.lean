import SystemE

namespace Elements.Book1

theorem helper_1_45_step1 (a b c d : Point) (AB BC CD AD DB : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine DB) (h5 : d.onLine DB) (h6 : d.onLine AD) (h7 : a.onLine AD)
    (h8 : AB ≠ DB) (h9 : DB ≠ AD) (h10 : AD ≠ AB)
    (h11 : b.onLine BC) (h12 : c.onLine BC) (h13 : b ≠ c)
    (h14 : c.onLine CD) (h15 : d.onLine CD) (h16 : BC ≠ CD) (h17 : CD ≠ DB) (h18 : DB ≠ BC)
    (h19 : ¬a.onLine DB) (h20 : ¬c.onLine DB) (h21 : ¬(a.sameSide c DB)) :
    distinctPointsOnLine d b DB := by
  euclid_finish

end Elements.Book1
