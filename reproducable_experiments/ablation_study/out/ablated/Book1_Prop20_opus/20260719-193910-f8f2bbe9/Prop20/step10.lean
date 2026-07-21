import SystemE
import Book1.Prop03.Main
import Book1.Prop05.Main
import Book1.Prop19.Main

namespace Elements.Book1

theorem helper_1_20_step10 (a b c : Point) (AB BC AC : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : AB ≠ BC) (h9 : BC ≠ AC) (h10 : AC ≠ AB) :
    |(b─c)| + |(c─a)| > |(a─b)| := by
  euclid_apply (extend_point_longer BC b c (c─a)) as d
  euclid_apply (proposition_3 c d c a BC AC) as e
  euclid_apply (line_from_points e a) as EA
  euclid_apply (extend_point AC c a) as f
  euclid_apply (proposition_5 c e a d f BC EA AC)
  euclid_apply (proposition_19 b a e AB EA BC)
  euclid_finish

end Elements.Book1
