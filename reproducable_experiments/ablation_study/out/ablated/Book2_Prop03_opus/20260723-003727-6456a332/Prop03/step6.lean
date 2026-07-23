import SystemE
import Book1.Prop30.Main

set_option systemE.solverTime 300

namespace Elements.Book2

open Elements.Book1

-- `AD` is the rectangle contained by `AC` and `CB`.  It is the parallelogram `AFDC`: base `AC`
-- (on `AB`), top `FD` (on `DE`), left side `AF`, right side `CD`.  `AF ∥ CD` is given; `AC ∥ FD`
-- is `AB ∥ DE`.  Orient it as `c a d f` (base `CA`, side `CD`, right angle at `D`), so
-- `rectangle_area` gives area `CA · CD`.  The right angle `∠ c:d:f` is the square's `∠ c:d:e`
-- (since `d` is between `e` and `f`, ray `d→f` = ray `d→e`).  Then `CA · CD = AC · CB` since
-- `|CD| = |CB|`.
theorem helper_2_3_step6 (a b c d e f : Point) (AB CD AF DE : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : c.onLine AB)
    (h4 : c.onLine CD) (h5 : d.onLine CD)
    (h6 : a.onLine AF) (h7 : f.onLine AF)
    (h8 : d.onLine DE) (h9 : e.onLine DE) (h10 : f.onLine DE)
    (h11 : ¬(DE.intersectsLine AB)) (h12 : ¬(AF.intersectsLine CD))
    (h13 : between a c b) (h14 : between e d f)
    (h15 : ∠ c:d:e = ∟)
    (h16 : |(c─d)| = |(c─b)|) :
    Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)| := by
  euclid_assert (∠ c:d:f = ∟)
  euclid_assert (formParallelogram c a d f AB DE CD AF)
  euclid_apply (rectangle_area c a d f AB DE CD AF)
  euclid_finish

end Elements.Book2
