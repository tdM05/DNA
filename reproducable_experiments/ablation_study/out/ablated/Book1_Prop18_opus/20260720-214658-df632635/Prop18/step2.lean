import SystemE

namespace Elements.Book1

theorem helper_1_18_step2 (a b c d : Point) (AB BC AC BD : Line)
    (h1 : b.onLine BD) (h2 : d.onLine BD)
    (h3 : a.onLine AB) (h4 : b.onLine AB) (h5 : a ≠ b)
    (h6 : b.onLine BC) (h7 : c.onLine BC)
    (h8 : c.onLine AC) (h9 : a.onLine AC)
    (h10 : AB ≠ BC) (h11 : BC ≠ AC) (h12 : AC ≠ AB)
    (h13 : between a d c) :
    distinctPointsOnLine b d BD := by
  euclid_finish

end Elements.Book1
