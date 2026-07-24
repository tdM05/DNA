import SystemE
import Book1.Prop30.Main

set_option systemE.solverTime 300
set_option maxHeartbeats 0

namespace Elements.Book2

-- The rectangle $AE$ (outer rectangle A B E F: bottom AB, top FE on DE, sides AF and BE) is split
-- by the interior segment CD (C on AB between A,B; D on DE between F,E) into the two rectangles
-- $AD$ (= A F D C) and the square $CE$ (= C D E B).  This is `sum_parallelograms_area` for the
-- parallelogram A B F E (a=A,b=B on AB; c=F,d=E on DE; AC=AF, BD=BE) with interior points
-- e=C on AB and f=D on DE.
theorem helper_2_3_step4 (a b c d e f : Point) (AB DE CD BE AF : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : c.onLine AB)
    (h4 : e.onLine DE) (h5 : d.onLine DE)
    (h6 : f.onLine AF) (h7 : a.onLine AF)
    (h8 : e.onLine BE) (h9 : b.onLine BE) (h10 : e ≠ b)
    (h11 : d.onLine CD) (h12 : c.onLine CD)
    (h13 : ¬(AF.intersectsLine CD)) (h14 : ¬(CD.intersectsLine BE))
    (h15 : ¬(DE.intersectsLine AB))
    (h16 : between a c b)
    (h17 : |(c─d)| = |(c─b)|) (h18 : |(b─e)| = |(c─b)|) (h19 : |(d─e)| = |(c─b)|)
    (h20 : ∠ b:c:d = ∟) (h21 : d.sameSide c BE)
    (hs2 : f.onLine DE ∧ between e d f) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b) := by
  euclid_apply (Elements.Book1.proposition_30 AF BE CD)
  have hafbe : ¬(AF.intersectsLine BE) := by euclid_finish
  euclid_apply (sum_parallelograms_area a b f e c d AB DE AF BE)
  euclid_finish

end Elements.Book2
