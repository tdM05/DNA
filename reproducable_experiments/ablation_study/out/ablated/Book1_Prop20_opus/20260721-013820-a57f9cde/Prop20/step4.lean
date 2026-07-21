import SystemE
import Book1.Prop05.Main

namespace Elements.Book1

theorem helper_1_20_step4 (a b c d d' : Point) (AB BC AC DC : Line)
    (h_da : |(d─a)| = |(a─c)|)
    (h1 : between a d d')
    (h2 : a.onLine AB) (h3 : b.onLine AB) (h4 : d'.onLine AB) (h5 : a ≠ b)
    (h6 : d.onLine DC) (h7 : c.onLine DC)
    (h8 : a.onLine AC) (h9 : c.onLine AC)
    (h10 : b.onLine BC) (h11 : c.onLine BC)
    (h12 : AB ≠ BC) (h13 : BC ≠ AC) (h14 : AC ≠ AB) :
    ∠ a:d:c = ∠ a:c:d := by
  euclid_apply (extend_point AC a c) as e
  euclid_apply (proposition_5 a d c d' e AB DC AC)
  euclid_finish

end Elements.Book1
