import SystemE
import Book1.Prop30.Main

set_option systemE.solverTime 300

namespace Elements.Book2

open Elements.Book1

-- `AE` is the rectangle contained by `AB` and `BC`: it is contained by `AB` and `BE`, and
-- `BE = BC`.  The rectangle `AFEB` is a parallelogram (base `AB`, top `DE`, sides `AF`, `BE`;
-- `AF ∥ BE` by Prop.~1.30).  Orient it as `b a e f` (base `BA`, side `BE`, right angle at `E`),
-- so `rectangle_area` gives its area as `BA · BE`.  The right angle `∠ b:e:f` is the square's
-- right angle `∠ b:e:d` (since `d` is between `e` and `f`, ray `e→f` = ray `e→d`).  Then
-- `BA · BE = AB · BC` since `|BE| = |CB|`.
theorem helper_2_3_step5 (a b c d e f : Point) (AB DE AF BE CD : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : c.onLine AB) (h4 : a ≠ b)
    (h5 : d.onLine DE) (h6 : e.onLine DE) (h7 : f.onLine DE)
    (h8 : a.onLine AF) (h9 : f.onLine AF)
    (h10 : b.onLine BE) (h11 : e.onLine BE) (h12 : e ≠ b)
    (h13 : c.onLine CD) (h14 : d.onLine CD)
    (h15 : ¬(DE.intersectsLine AB)) (h16 : ¬(AF.intersectsLine CD)) (h17 : ¬(CD.intersectsLine BE))
    (h18 : d.sameSide c BE)
    (h19 : between e d f)
    (h20 : ∠ b:e:d = ∟)
    (h21 : |(b─e)| = |(c─b)|) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)| := by
  euclid_apply (proposition_30 AF BE CD)
  euclid_apply (parallelogram_same_side d e c b DE AB CD BE)
  euclid_assert (∠ b:e:f = ∟)
  euclid_assert (formParallelogram b a e f AB DE BE AF)
  euclid_apply (rectangle_area b a e f AB DE BE AF)
  euclid_finish

end Elements.Book2
