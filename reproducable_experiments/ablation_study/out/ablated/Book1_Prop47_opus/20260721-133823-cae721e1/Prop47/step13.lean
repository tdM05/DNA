import SystemE
import Book1.Prop41.Main

set_option systemE.solverTime 25

namespace Elements.Book1

theorem helper_1_47_step13 (a b d l m : Point) (AL BD DE BC AD AB : Line)
    (h1 : l.onLine AL) (h2 : m.onLine AL) (h3 : a.onLine AL)
    (h4 : d.onLine BD) (h5 : b.onLine BD)
    (h6 : l.onLine DE) (h7 : d.onLine DE)
    (h8 : m.onLine BC) (h9 : b.onLine BC)
    (h10 : a.onLine AD) (h11 : d.onLine AD)
    (h12 : a.onLine AB) (h13 : b.onLine AB)
    (h14 : ¬(AL.intersectsLine BD)) (h15 : ¬(DE.intersectsLine BC))
    (h16 : ¬(a.onLine BD))
    (h17 : b.onLine BD ∧ d.onLine BD ∧ ¬(BD.intersectsLine AL)) :
    Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:b:d + Triangle.area △ a:b:d := by
  euclid_apply (proposition_41 l d b m a AL BD DE BC AD AB)
  euclid_finish

end Elements.Book1
