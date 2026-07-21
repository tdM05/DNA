import SystemE

namespace Elements.Book1

theorem helper_1_47_step15 (a b d f c : Point) :
    Triangle.area △ a:b:d = Triangle.area △ f:b:c →
      Triangle.area △ a:b:d + Triangle.area △ a:b:d =
        Triangle.area △ f:b:c + Triangle.area △ f:b:c := by
  euclid_finish

end Elements.Book1
