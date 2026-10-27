import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Sentence 1.36.9: pure transitivity of the two area equalities step7 (EBCH = ABCD) and step8
-- (EFGH = EBCH) ⟹ ABCD = EFGH.
theorem helper_1_36_step9 (a b c d e f g h : Point)
    (step7 : Triangle.area △ e:b:h + Triangle.area △ c:b:h
              = Triangle.area △ a:b:d + Triangle.area △ d:b:c)
    (step8 : Triangle.area △ e:f:h + Triangle.area △ h:f:g
              = Triangle.area △ e:b:h + Triangle.area △ c:b:h) :
    Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g := by
  linarith [step7, step8]

end Elements.Book1
