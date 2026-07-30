import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_41_s4
    (s2 : Triangle.area △ a:b:c = Triangle.area △ e:b:c)
    (s3 : Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ a:b:c + Triangle.area △ a:b:c) :
    Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ e:b:c + Triangle.area △ e:b:c := by
  linarith

end Elements.Book1
