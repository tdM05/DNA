import SystemE
import Book1.Prop41.Main

namespace Elements.Book1

theorem helper_1_47_step13 (a b d l m : Point) (AL BD BC DE AB AD : Line)
    (hassum : b.onLine BD ∧ d.onLine BD ∧ ¬(BD.intersectsLine AL))
    (h1 : m.onLine AL) (h2 : l.onLine AL)
    (h3 : m.onLine BC) (h4 : b.onLine BC)
    (h5 : l.onLine DE) (h6 : d.onLine DE)
    (h7 : a.onLine AL)
    (h8 : a.onLine AB) (h9 : b.onLine AB) (h10 : a ≠ b)
    (h11 : a.onLine AD) (h12 : d.onLine AD)
    (h13 : ¬(DE.intersectsLine BC)) (h14 : ¬(a.onLine BD))
    (h15 : DE ≠ BC) (h16 : ¬(d.onLine AB)) (h17 : a ≠ d) (h18 : b ≠ d) (h19 : b ≠ m) :
    Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:b:d + Triangle.area △ a:b:d := by
  have hpara : formParallelogram m l b d AL BD BC DE := by euclid_finish
  have htri : formTriangle a b d AB BD AD := by euclid_finish
  euclid_apply (proposition_41 m b d l a AL BD BC DE AB AD)
  euclid_apply (parallelogram_area m l b d AL BD BC DE)
  euclid_finish

end Elements.Book1
