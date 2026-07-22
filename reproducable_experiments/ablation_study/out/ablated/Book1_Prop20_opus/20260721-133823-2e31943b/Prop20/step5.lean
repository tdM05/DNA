import SystemE

namespace Elements.Book1

theorem helper_1_20_step5 (a b c d d' : Point) (AB BC AC : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : AB ≠ BC) (h9 : BC ≠ AC) (h10 : AC ≠ AB)
    (h11 : d'.onLine AB) (h12 : between a d d')
    (h13 : between b a d)
    (h14 : ∠ a:d:c = ∠ a:c:d) :
    ∠ b:c:d > ∠ a:d:c := by
  euclid_finish

end Elements.Book1
