import SystemE
import Book1.Prop34.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step2
  (a h e k : Point) (AD EF AB GH AC : Line)
  (hassump1 : formParallelogram a h e k AD EF AB GH ∧ distinctPointsOnLine a k AC)
  : Triangle.area △ a:e:k = Triangle.area △ a:h:k := by
  obtain ⟨hpara, hak⟩ := hassump1
  euclid_apply (proposition_34 h k a e GH AB AD EF AC)
  euclid_finish

end Elements.Book1
