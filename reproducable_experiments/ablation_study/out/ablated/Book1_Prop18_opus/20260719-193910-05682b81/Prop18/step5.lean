import SystemE

namespace Elements.Book1

theorem helper_1_18_step5 (a b c d : Point) (AB BC AC : Line)
    (h1 : ∠ a:d:b > ∠ d:c:b)
    (h2 : ∠ a:d:b = ∠ a:b:d)
    (h3 : between a d c)
    (h4 : a.onLine AC) (h5 : c.onLine AC)
    (h6 : a.onLine AB) (h7 : b.onLine AB) (h8 : a ≠ b)
    (h9 : b.onLine BC) (h10 : c.onLine BC) (h11 : AC ≠ AB) :
    ∠ a:b:d > ∠ b:c:a := by
  euclid_finish

end Elements.Book1
