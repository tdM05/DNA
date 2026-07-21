import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step5
  (f g h k m : Point)
  (step4 : ∠ h:k:f = ∠ g:h:m) :
  ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g := by
  rw [step4]

end Elements.Book1
