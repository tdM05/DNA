import SystemE
import Book1Variants.Prop05

namespace Elements.Book1

theorem helper_1_18_step4 (a b c d : Point) (AB AC BD : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BD) (h5 : d.onLine BD)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : between a d c)
    (h9 : |(a─b)| = |(a─d)|)
    (h10 : AC ≠ AB) :
    ∠ a:d:b = ∠ a:b:d := by
  euclid_apply (proposition_5' a b d AB BD AC)
  euclid_finish

end Elements.Book1
