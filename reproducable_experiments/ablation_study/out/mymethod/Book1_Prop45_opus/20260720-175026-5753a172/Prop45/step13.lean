import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step13
  (f g h l m : Point)
  (step12 : ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l) :
  ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l := by
  exact step12

end Elements.Book1
