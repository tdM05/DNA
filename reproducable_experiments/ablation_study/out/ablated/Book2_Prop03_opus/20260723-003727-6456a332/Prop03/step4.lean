import SystemE
import Book1.Prop30.Main

set_option systemE.solverTime 300

namespace Elements.Book2

open Elements.Book1

-- The rectangle `AE` (= `AFEB`) equals the rectangle `AD` (= `AFDC`) plus the square `CE`
-- (= `CDEB`).  `AFEB` is a parallelogram: base `AB` (points `a`, `b`), top line `DE` (points
-- `f`, `d`, `e`), left side `AF` (points `a`, `f`), right side `BE` (points `b`, `e`).  `AF ∥ BE`
-- follows from `AF ∥ CD` and `CD ∥ BE` (Prop.~1.30); `AB ∥ DE` is the square's side.  The base is
-- cut at `c` (between `a`, `b`) and the top at `d` (between `f`, `e`), so splitting along `CD`
-- (`sum_parallelograms_area`) yields the two triangle-pairs of `AFDC` and `CDEB`.
theorem helper_2_3_step4 (a b c d e f : Point) (AB DE AF BE CD : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : c.onLine AB) (h4 : a ≠ b)
    (h5 : d.onLine DE) (h6 : e.onLine DE) (h7 : f.onLine DE)
    (h8 : a.onLine AF) (h9 : f.onLine AF)
    (h10 : b.onLine BE) (h11 : e.onLine BE) (h12 : e ≠ b)
    (h13 : c.onLine CD) (h14 : d.onLine CD)
    (h15 : ¬(DE.intersectsLine AB)) (h16 : ¬(AF.intersectsLine CD)) (h17 : ¬(CD.intersectsLine BE))
    (h18 : d.sameSide c BE)
    (h19 : between a c b) (h20 : between e d f) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b) := by
  euclid_apply (proposition_30 AF BE CD)
  euclid_apply (between_symm e d f)
  euclid_apply (parallelogram_same_side d e c b DE AB CD BE)
  euclid_assert (formParallelogram a b f e AB DE AF BE)
  euclid_apply (sum_parallelograms_area a b f e c d AB DE AF BE)
  euclid_finish

end Elements.Book2
