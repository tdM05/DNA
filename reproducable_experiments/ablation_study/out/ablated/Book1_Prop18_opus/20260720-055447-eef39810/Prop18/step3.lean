import SystemE
import Book1.Prop16.Main

namespace Elements.Book1

theorem helper_1_18_step3 (a b c d : Point) (AB BC AC BD : Line)
    (h1 : between a d c)
    (h2 : b.onLine BC) (h3 : c.onLine BC)
    (h4 : c.onLine AC) (h5 : a.onLine AC)
    (h6 : b.onLine BD) (h7 : d.onLine BD)
    (h8 : a.onLine AB) (h9 : b.onLine AB) (h10 : a ≠ b)
    (h11 : AB ≠ BC) (h12 : BC ≠ AC) (h13 : AC ≠ AB) :
    ∠ a:d:b > ∠ d:c:b := by
  euclid_apply (proposition_16 b c d a BC AC BD)
  euclid_finish

end Elements.Book1
