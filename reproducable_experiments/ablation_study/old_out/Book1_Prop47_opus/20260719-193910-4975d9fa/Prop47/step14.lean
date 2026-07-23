import SystemE
import Book1.Prop41.Main

namespace Elements.Book1

theorem helper_1_47_step14 (a b c f g : Point) (AG BF AB GF BC FC : Line)
    (hpara : formParallelogram a g b f AG BF AB GF)
    (htri : formTriangle c b f BC BF FC)
    (hcAG : c.onLine AG)
    (hpar : ¬(AG.intersectsLine BF)) :
    Triangle.area △ a:g:f + Triangle.area △ a:f:b =
      Triangle.area △ f:b:c + Triangle.area △ f:b:c := by
  euclid_apply (proposition_41 a b f g c AG BF AB GF BC FC)
  euclid_finish

end Elements.Book1
