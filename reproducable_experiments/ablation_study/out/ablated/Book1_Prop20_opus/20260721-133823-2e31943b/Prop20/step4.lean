import SystemE
import Book1Variants.Prop05

namespace Elements.Book1

theorem helper_1_20_step4 (a b c d d' : Point) (AB BC AC DC : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : AB ≠ BC) (h9 : BC ≠ AC) (h10 : AC ≠ AB)
    (h11 : d'.onLine AB) (h12 : between a d d')
    (h13 : d.onLine DC) (h14 : c.onLine DC)
    (h15 : |(d─a)| = |(a─c)|) :
    ∠ a:d:c = ∠ a:c:d := by
  euclid_apply (proposition_5' a d c AB DC AC)
  euclid_finish

end Elements.Book1
