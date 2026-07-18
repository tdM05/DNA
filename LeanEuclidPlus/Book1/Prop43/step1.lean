import SystemE
import Book1.Prop34.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_43_step1
  (a b c d : Point) (AD BC AB CD AC : Line)
  (hassump1 : formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC)
  : Triangle.area △ a:b:c = Triangle.area △ a:c:d := by
  obtain ⟨hpara, hac⟩ := hassump1
  euclid_apply (proposition_34 b a c d AB CD BC AD AC)
  euclid_finish

end Elements.Book1
