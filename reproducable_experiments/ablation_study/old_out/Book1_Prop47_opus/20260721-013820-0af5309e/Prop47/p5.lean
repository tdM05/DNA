import SystemE

namespace Elements.Book1

theorem probe_s4 (a b c f : Point) (AB BC BF : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : f.onLine BF) (h7 : b.onLine BF)
    (h10 : ∠ a:b:f = ∟) (h11 : ∠ b:a:c = ∟)
    (h13 : ¬(a.onLine BF)) (h15 : ¬(c.onLine AB)) (h16 : ¬(c.onLine BF))
    (h17 : |(b─f)| = |(a─b)|) :
    c.sameSide a BF := by
  euclid_finish
end Elements.Book1
