import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step4 (a f g h k : Point)
    (hstep2 : ∠ a:g:k = ∠ g:h:f)
    : ∠ a:g:k = ∠ g:h:f := by
  exact hstep2

end Elements.Book1
