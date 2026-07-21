import SystemE
import Book1.Prop03.Main
import Book1.Prop05.Main
import Book1.Prop19.Main

namespace Elements.Book1

theorem helper_1_20_step9 (a b c : Point) (AB BC AC : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : AB ≠ BC) (h9 : BC ≠ AC) (h10 : AC ≠ AB) :
    |(a─b)| + |(b─c)| > |(a─c)| := by
  euclid_apply (extend_point_longer AB a b (b─c)) as d
  euclid_apply (proposition_3 b d b c AB BC) as e
  euclid_apply (line_from_points e c) as EC
  euclid_apply (extend_point BC b c) as f
  euclid_apply (proposition_5 b e c d f AB EC BC)
  euclid_apply (proposition_19 a c e AC EC AB)
  euclid_finish

end Elements.Book1
