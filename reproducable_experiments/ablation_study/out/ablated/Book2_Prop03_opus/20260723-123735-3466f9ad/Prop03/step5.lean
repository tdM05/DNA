import SystemE
import Book1.Prop30.Main

set_option systemE.solverTime 300
set_option maxHeartbeats 0

namespace Elements.Book2

-- $AE$ is the rectangle contained by $AB$ and $BE$, and $BE = BC$.  Apply `rectangle_area` at the
-- corner $B$: parallelogram (b a e f) with side B-A on AB, adjacent side B-E on BE, opposite side
-- E-F on DE, remaining side A-F on AF.  The right angle is ∠ B:E:F (= the square corner ∠ B:E:D,
-- since F lies on ray E→D past D).  Its area (△ A:B:E + △ A:F:E) equals |B─A| · |B─E| =
-- |A─B| · |B─C|.
theorem helper_2_3_step5 (a b c d e f : Point) (AB DE CD BE AF : Line)
    (h1 : e.onLine DE) (h2 : d.onLine DE)
    (h3 : a.onLine AB) (h4 : b.onLine AB) (h5 : c.onLine AB)
    (h6 : a.onLine AF) (h7 : f.onLine AF)
    (h9 : e.onLine BE) (h10 : b.onLine BE) (h11 : e ≠ b)
    (h12 : d.onLine CD) (h13 : c.onLine CD)
    (h14 : ¬(AF.intersectsLine CD)) (h15 : ¬(CD.intersectsLine BE))
    (h16 : ¬(DE.intersectsLine AB))
    (h17 : between a c b)
    (h18 : |(c─d)| = |(c─b)|) (h19 : |(d─e)| = |(c─b)|)
    (h20 : ∠ b:c:d = ∟) (h21 : ∠ b:e:d = ∟) (h22 : ∠ c:b:e = ∟)
    (hs2 : f.onLine DE ∧ between e d f)
    (step5_assumption1 : |(b─e)| = |(c─b)|) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)| := by
  euclid_apply (Elements.Book1.proposition_30 AF BE CD)
  have hafbe : ¬(AF.intersectsLine BE) := by euclid_finish
  have hbef : ∠ b:e:f = ∟ := by euclid_finish
  euclid_apply (rectangle_area b a e f AB DE BE AF)
  euclid_finish

end Elements.Book2
