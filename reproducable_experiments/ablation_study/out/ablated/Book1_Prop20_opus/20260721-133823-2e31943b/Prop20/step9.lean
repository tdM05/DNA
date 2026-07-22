import SystemE
import Book1.Prop20.ineq

namespace Elements.Book1

theorem helper_1_20_step9 (a b c : Point) (AB BC AC : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : AB ≠ BC) (h9 : BC ≠ AC) (h10 : AC ≠ AB) :
    |(a─b)| + |(b─c)| > |(a─c)| := by
  euclid_apply (helper_1_20_ineq a b c AB BC AC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
  euclid_finish

end Elements.Book1
