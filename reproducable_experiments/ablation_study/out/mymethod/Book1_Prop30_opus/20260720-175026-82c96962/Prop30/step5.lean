import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step5 (a d f g h k : Point)
    (hstep4 : ∠ a:g:k = ∠ g:h:f) (hstep3 : ∠ g:h:f = ∠ g:k:d)
    : ∠ a:g:k = ∠ g:k:d := by
  rw [hstep4]; exact hstep3

end Elements.Book1
