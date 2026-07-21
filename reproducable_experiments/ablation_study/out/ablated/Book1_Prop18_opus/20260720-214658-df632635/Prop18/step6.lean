import SystemE

namespace Elements.Book1

theorem helper_1_18_step6 (a b c d : Point) (AB BC AC : Line)
    (h1 : ∠ a:b:d > ∠ b:c:a)
    (h2 : between a d c)
    (h3 : a.onLine AB) (h4 : b.onLine AB) (h5 : a ≠ b)
    (h6 : b.onLine BC) (h7 : c.onLine BC)
    (h8 : c.onLine AC) (h9 : a.onLine AC)
    (h10 : AC ≠ AB) :
    ∠ a:b:c > ∠ b:c:a := by
  euclid_finish

end Elements.Book1
