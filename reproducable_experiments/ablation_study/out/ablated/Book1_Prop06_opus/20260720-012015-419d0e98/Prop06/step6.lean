import SystemE

namespace Elements.Book1

theorem helper_1_6_step6 (a b c d : Point) (AB BC AC : Line)
    (h1 : between b d a)
    (h2 : ∠ a:b:c = ∠ a:c:b)
    (h3 : a.onLine AB) (h4 : b.onLine AB) (h5 : a ≠ b)
    (h6 : b.onLine BC) (h7 : c.onLine BC)
    (h8 : c.onLine AC) (h9 : a.onLine AC)
    (h10 : AB ≠ BC) (h11 : BC ≠ AC) (h12 : AC ≠ AB) :
    ∠ d:b:c = ∠ a:c:b := by
  euclid_finish

end Elements.Book1
