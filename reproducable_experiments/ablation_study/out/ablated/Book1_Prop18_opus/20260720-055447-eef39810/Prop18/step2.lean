import SystemE

namespace Elements.Book1

theorem helper_1_18_step2 (a b c d : Point) (AB AC BD : Line)
    (h1 : b.onLine BD) (h2 : d.onLine BD) (h3 : between a d c)
    (h4 : a.onLine AB) (h5 : b.onLine AB) (h6 : a ≠ b)
    (h7 : a.onLine AC) (h8 : c.onLine AC) (h9 : AC ≠ AB) :
    distinctPointsOnLine b d BD := by
  euclid_finish

end Elements.Book1
