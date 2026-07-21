import SystemE

namespace Elements.Book1

theorem helper_1_20_step5 (a b c d d' : Point) (AB BC AC DC : Line)
    (h1 : between b a d) (h2 : between a d d')
    (h3 : ∠ a:d:c = ∠ a:c:d)
    (h4 : a.onLine AB) (h5 : b.onLine AB) (h6 : d'.onLine AB) (h7 : a ≠ b)
    (h8 : b.onLine BC) (h9 : c.onLine BC)
    (h10 : c.onLine AC) (h11 : a.onLine AC)
    (h12 : d.onLine DC) (h13 : c.onLine DC)
    (h14 : AB ≠ BC) (h15 : BC ≠ AC) (h16 : AC ≠ AB) :
    ∠ b:c:d > ∠ a:d:c := by
  euclid_finish

end Elements.Book1
