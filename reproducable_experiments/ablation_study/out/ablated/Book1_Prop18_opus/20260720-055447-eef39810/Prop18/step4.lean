import SystemE
import Book1Variants.Prop05

namespace Elements.Book1

theorem helper_1_18_step4 (a b c d : Point) (AB AC BD : Line)
    (h1 : |(a─b)| = |(a─d)|)
    (h2 : between a d c)
    (h3 : a.onLine AC) (h4 : c.onLine AC)
    (h5 : d.onLine BD) (h6 : b.onLine BD)
    (h7 : a.onLine AB) (h8 : b.onLine AB) (h9 : a ≠ b)
    (h10 : AC ≠ AB) :
    ∠ a:d:b = ∠ a:b:d := by
  euclid_apply (proposition_5' a d b AC BD AB)
  euclid_finish

end Elements.Book1
