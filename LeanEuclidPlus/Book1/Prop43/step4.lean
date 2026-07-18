import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step4
  (a c e f g h k : Point)
  (hassump1 : Triangle.area △ a:e:k = Triangle.area △ a:h:k ∧ Triangle.area △ k:f:c = Triangle.area △ k:g:c)
  : Triangle.area △ a:e:k + Triangle.area △ k:g:c = Triangle.area △ a:h:k + Triangle.area △ k:f:c := by
  obtain ⟨h1, h2⟩ := hassump1
  linarith [h1, h2]

end Elements.Book1
