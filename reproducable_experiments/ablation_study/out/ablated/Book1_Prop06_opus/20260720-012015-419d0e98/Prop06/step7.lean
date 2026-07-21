import SystemE
import Book1.Prop04.Main

namespace Elements.Book1

theorem helper_1_6_step7 (a b c d : Point) (AB BC AC DC : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : AB ≠ BC) (h9 : BC ≠ AC) (h10 : AC ≠ AB)
    (h11 : between b d a)
    (h12 : d.onLine DC) (h13 : c.onLine DC)
    (h14 : |(b─d)| = |(a─c)|)
    (h15 : ∠ d:b:c = ∠ a:c:b) :
    |(d─c)| = |(a─b)| := by
  euclid_apply (proposition_4 b d c c a b AB DC BC AC AB BC)
  euclid_finish

end Elements.Book1
