import SystemE
import Book1.Prop47.dec18

namespace Elements.Book1

theorem helper_1_47_step18fin (a b c d e f g h k l m : Point)
    (hdec : Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ b:m:l + Triangle.area △ b:l:d) +
      (Triangle.area △ c:e:l + Triangle.area △ c:l:m))
    (h16 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b)
    (h17 : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c) := by
  euclid_finish

theorem helper_1_47_step18 (a b c d e f g h k l m : Point) (AL BC BD CE DE : Line)
    (h1 : d.onLine DE) (h2 : e.onLine DE) (h3 : l.onLine DE)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : m.onLine BC)
    (h7 : d.onLine BD) (h8 : b.onLine BD)
    (h9 : e.onLine CE) (h10 : c.onLine CE) (hec : e ≠ c)
    (h11 : m.onLine AL) (h12 : l.onLine AL)
    (h13 : ¬(DE.intersectsLine BC)) (h14 : ¬(BD.intersectsLine CE))
    (h15 : ¬(AL.intersectsLine BD)) (h16 : d.sameSide b CE) (h17 : m.sameSide b DE)
    (h18 : between b m c) (h19 : between d l e)
    (hstep16 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b)
    (hstep17 : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c) := by
  have hdec := helper_1_47_dec18 b c d e l m AL BC BD CE DE
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hec h11 h12 h13 h14 h15 h16 h17 h18 h19
  exact helper_1_47_step18fin a b c d e f g h k l m hdec hstep16 hstep17

end Elements.Book1
