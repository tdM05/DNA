import SystemE

namespace Elements.Book1

theorem helper_1_18_step2 (a b c d : Point) (AB AC BD : Line)
    (h1 : b.onLine BD) (h2 : d.onLine BD)
    (h3 : between a d c)
    (h4 : a.onLine AC) (h5 : c.onLine AC)
    (h6 : a.onLine AB) (h7 : b.onLine AB)
    (h8 : a ≠ b) (h9 : AC ≠ AB) :
    distinctPointsOnLine b d BD := by
  euclid_finish

end Elements.Book1
