import SystemE

namespace Elements.Book1

theorem helper_1_20_step3 (a b c d d' : Point) (AB BC AC DC : Line)
    (h1 : d.onLine DC) (h2 : c.onLine DC) (h3 : between a d d')
    (h4 : a.onLine AB) (h5 : d'.onLine AB) (h6 : b.onLine AB) (h7 : a ≠ b)
    (h8 : b.onLine BC) (h9 : c.onLine BC)
    (h10 : c.onLine AC) (h11 : a.onLine AC)
    (h12 : AB ≠ BC) (h13 : BC ≠ AC) (h14 : AC ≠ AB) :
    distinctPointsOnLine d c DC := by
  euclid_finish

end Elements.Book1
