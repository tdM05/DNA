import SystemE

namespace Elements.Book1

theorem helper_1_20_step5 (a b c d : Point) (AB BC AC : Line)
    (h1 : between b a d) (h2 : ∠ a:d:c = ∠ a:c:d)
    (h3 : a.onLine AB) (h4 : b.onLine AB) (h5 : a ≠ b)
    (h6 : b.onLine BC) (h7 : c.onLine BC)
    (h8 : c.onLine AC) (h9 : a.onLine AC)
    (h10 : AB ≠ BC) (h11 : BC ≠ AC) (h12 : AC ≠ AB) :
    ∠ b:c:d > ∠ a:d:c := by
  euclid_finish

end Elements.Book1
