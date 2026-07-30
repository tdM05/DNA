import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_43_s4
    (a e k g h f c : Point)
    (hassump1 : Triangle.area △ a:e:k = Triangle.area △ a:h:k ∧
                Triangle.area △ k:f:c = Triangle.area △ k:g:c)
    (s2 : Triangle.area △ a:e:k = Triangle.area △ a:h:k)
    (s3 : Triangle.area △ k:f:c = Triangle.area △ k:g:c)
    : Triangle.area △ a:e:k + Triangle.area △ k:g:c =
      Triangle.area △ a:h:k + Triangle.area △ k:f:c := by
  linarith

end Elements.Book1
