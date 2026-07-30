import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_36_s9 (a b c d e f g h : Point)
  (h_s7 : Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c)
  (h_s8 : Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h) :
  Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g := by
  linarith

end Elements.Book1
