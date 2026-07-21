import SystemE
import Book1.Prop41.Main

namespace Elements.Book1

theorem helper_1_47_step13 (a b d l m : Point) (AL BD DE BC AD AB : Line)
    (hpara : formParallelogram l m d b AL BD DE BC)
    (htri : formTriangle a d b AD BD AB)
    (haAL : a.onLine AL)
    (hpar : ¬(AL.intersectsLine BD)) :
    Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:b:d + Triangle.area △ a:b:d := by
  euclid_apply (proposition_41 l d b m a AL BD DE BC AD AB)
  euclid_finish

end Elements.Book1
