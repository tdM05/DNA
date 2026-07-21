import SystemE
import Book1.Prop19.Main

namespace Elements.Book1

theorem helper_1_20_step6 (a b c d d' : Point) (AB BC AC DC : Line)
    (h1 : ∠ b:c:d > ∠ b:d:c)
    (h2 : a.onLine AB) (h3 : b.onLine AB) (h4 : a ≠ b)
    (h5 : b.onLine BC) (h6 : c.onLine BC)
    (h7 : c.onLine AC) (h8 : a.onLine AC)
    (h9 : AB ≠ BC) (h10 : BC ≠ AC) (h11 : AC ≠ AB)
    (h12 : d'.onLine AB) (h13 : between a d d')
    (h14 : d.onLine DC) (h15 : c.onLine DC) :
    |(d─b)| > |(b─c)| := by
  euclid_apply (proposition_19 b c d BC DC AB)
  euclid_finish

end Elements.Book1
