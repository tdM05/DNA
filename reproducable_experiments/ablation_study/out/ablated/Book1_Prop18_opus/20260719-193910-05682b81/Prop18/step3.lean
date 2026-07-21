import SystemE
import Book1.Prop16.Main

namespace Elements.Book1

theorem helper_1_18_step3 (a b c d : Point) (AB BC AC BD : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : AB ≠ BC) (h9 : BC ≠ AC) (h10 : AC ≠ AB)
    (h11 : between a d c)
    (h12 : b.onLine BD) (h13 : d.onLine BD) :
    ∠ a:d:b > ∠ d:c:b := by
  euclid_apply (proposition_16 b c d a BC AC BD)
  euclid_finish

end Elements.Book1
