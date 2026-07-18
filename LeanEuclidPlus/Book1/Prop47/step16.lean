import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step16
    (a b c d f g l m : Point)
    (hstep13 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:b:d + Triangle.area △ a:b:d)
    (hstep14 : Triangle.area △ a:g:f + Triangle.area △ a:f:b =
      Triangle.area △ f:b:c + Triangle.area △ f:b:c)
    (hstep12 : Triangle.area △ a:b:d = Triangle.area △ f:b:c) :
    Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b := by
  linarith [hstep13, hstep14, hstep12]

end Elements.Book1
