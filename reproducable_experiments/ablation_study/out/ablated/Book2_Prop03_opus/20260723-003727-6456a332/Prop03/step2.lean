import SystemE
import Book1.Prop30.Main

set_option systemE.solverTime 300

namespace Elements.Book2

open Elements.Book1

-- `ED` is drawn through to `F`.  `f` (= AF ∩ DE) already lies on `DE`; the content is that `d`
-- lies between `e` and `f`.  The square's left side `CD` passes through the cut-point `c`, which
-- lies between `a` and `b` on `AB`, so `CD` separates `a` from `b` (Pasch 3).  From the square
-- `CDEB`, `e` lies on `b`'s side of `CD` (parallelogram_same_side); and since `AF ∥ CD` with
-- `a, f ∈ AF`, `f` lies on `a`'s side of `CD`.  So `f` and `e` are on opposite sides of `CD`, and
-- `d` (= CD ∩ DE) lies between them (Pasch 4).  `AF ∥ BE` (Prop.~1.30) forces `f ≠ e`.
theorem helper_2_3_step2 (a b c d e f : Point) (AB CD DE BE AF : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : c.onLine AB) (h4 : a ≠ b) (h5 : between a c b)
    (h6 : c.onLine CD) (h7 : d.onLine CD)
    (h8 : d.onLine DE) (h9 : e.onLine DE) (h10 : f.onLine DE)
    (h11 : e.onLine BE) (h12 : b.onLine BE) (h13 : e ≠ b) (h14 : d.sameSide c BE)
    (h15 : ¬(DE.intersectsLine AB)) (h16 : ¬(CD.intersectsLine BE))
    (h17 : a.onLine AF) (h18 : f.onLine AF) (h19 : ¬(AF.intersectsLine CD)) :
    f.onLine DE ∧ between e d f := by
  euclid_apply (proposition_30 AF BE CD)
  euclid_apply (parallelogram_same_side d e c b DE AB CD BE)
  euclid_apply (pasch_3 a c b CD)
  euclid_apply (pasch_4 e d f CD DE)
  euclid_finish

end Elements.Book2
