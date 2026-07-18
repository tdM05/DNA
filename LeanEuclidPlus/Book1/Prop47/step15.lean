import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step15
    (a b c d f : Point) :
    Triangle.area △ a:b:d = Triangle.area △ f:b:c →
      Triangle.area △ a:b:d + Triangle.area △ a:b:d =
        Triangle.area △ f:b:c + Triangle.area △ f:b:c := by
  intro h
  rw [h]

end Elements.Book1
