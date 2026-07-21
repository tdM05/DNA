import SystemE
import Book1.Prop19.Main

namespace Elements.Book1

theorem helper_1_20_step6 (a b c d d' : Point) (AB BC AC DC : Line)
    (h_angle : ∠ b:c:d > ∠ b:d:c)
    (h1 : between a d d')
    (h2 : a.onLine AB) (h3 : b.onLine AB) (h4 : d'.onLine AB) (h5 : a ≠ b)
    (h6 : b.onLine BC) (h7 : c.onLine BC)
    (h8 : d.onLine DC) (h9 : c.onLine DC)
    (h10 : c.onLine AC) (h11 : a.onLine AC)
    (h12 : AB ≠ BC) (h13 : BC ≠ AC) (h14 : AC ≠ AB) :
    |(d─b)| > |(b─c)| := by
  euclid_apply (proposition_19 b c d BC DC AB)
  euclid_finish

end Elements.Book1
