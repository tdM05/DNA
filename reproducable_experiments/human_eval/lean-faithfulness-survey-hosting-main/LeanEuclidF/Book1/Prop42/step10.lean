import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_42_s10 (a b c e f g : Point)
    (s8 : Triangle.area △ a:b:c = Triangle.area △ a:e:c + Triangle.area △ a:e:c)
    (s9 : Triangle.area △ f:e:c + Triangle.area △ f:c:g = Triangle.area △ a:e:c + Triangle.area △ a:e:c) :
    Triangle.area △ f:e:c + Triangle.area △ f:c:g = Triangle.area △ a:b:c := by
  linarith

end Elements.Book1
