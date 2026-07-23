import SystemE

namespace Elements.Book1

theorem probe_s2 (a b c d : Point) (AB BC BD : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h8 : d.onLine BD) (h9 : b.onLine BD)
    (h10 : ∠ c:b:d = ∟) (h11 : ∠ b:a:c = ∟)
    (h12 : ¬(d.onLine BC)) (h13 : ¬(a.onLine BC)) (h14 : ¬(d.sameSide a BC))
    (h15 : ¬(c.onLine AB)) (h16 : ¬(d.onLine AB))
    (h17 : |(b─d)| = |(b─c)|) :
    d.sameSide c AB := by
  euclid_finish
end Elements.Book1
