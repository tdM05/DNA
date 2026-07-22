import SystemE
import Book1.Prop03.Main
import Book1Variants.Prop05
import Book1.Prop19.Main

namespace Elements.Book1

/-- A single triangle inequality `|xy| + |yz| > |xz|`, proved by the construction of
Euclid's Prop.~1.20 (extend `xy` beyond the apex `y`, cut off a segment equal to `yz`
[Prop.~1.3], join, use the isosceles base angles [Prop.~1.5] and Prop.~1.19). -/
theorem helper_1_20_ineq (x y z : Point) (XY YZ XZ : Line)
    (h1 : x.onLine XY) (h2 : y.onLine XY) (h3 : x ≠ y)
    (h4 : y.onLine YZ) (h5 : z.onLine YZ)
    (h6 : z.onLine XZ) (h7 : x.onLine XZ)
    (h8 : XY ≠ YZ) (h9 : YZ ≠ XZ) (h10 : XZ ≠ XY) :
    |(x─y)| + |(y─z)| > |(x─z)| := by
  euclid_apply (extend_point_longer XY x y (z─y)) as d'
  euclid_apply (proposition_3 y d' y z XY YZ) as d
  euclid_apply (line_from_points d z) as DZ
  euclid_apply (proposition_5' y d z XY DZ YZ)
  have hbtw : between x y d := by euclid_finish
  have hangle : ∠ x:z:d > ∠ z:d:x := by euclid_finish
  euclid_apply (proposition_19 x z d XZ DZ XY)
  euclid_finish

end Elements.Book1
