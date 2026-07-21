import SystemE

namespace Elements.Book1

theorem helper_1_18_step5 (a b c d : Point) (AB BC AC : Line)
    (h1 : ∠ a:d:b > ∠ d:c:b) (h2 : ∠ a:d:b = ∠ a:b:d) (h3 : between a d c)
    (h4 : a.onLine AB) (h5 : b.onLine AB) (h6 : a ≠ b)
    (h7 : b.onLine BC) (h8 : c.onLine BC)
    (h9 : c.onLine AC) (h10 : a.onLine AC)
    (h11 : AB ≠ BC) (h12 : BC ≠ AC) (h13 : AC ≠ AB) :
    ∠ a:b:d > ∠ b:c:a := by
  euclid_finish

end Elements.Book1
