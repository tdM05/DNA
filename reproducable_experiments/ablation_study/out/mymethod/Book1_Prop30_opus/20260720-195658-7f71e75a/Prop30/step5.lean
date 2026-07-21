import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step5 (a g h k d f : Point)
  (hstep4 : ∠ a:g:k = ∠ g:h:f) (hstep3 : ∠ g:h:f = ∠ g:k:d) : ∠ a:g:k = ∠ g:k:d := by
  rw [hstep4]; exact hstep3

end Elements.Book1
