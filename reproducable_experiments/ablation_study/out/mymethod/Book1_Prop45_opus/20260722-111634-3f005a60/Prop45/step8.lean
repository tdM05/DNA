import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step8 (f g h k m : Point)
    (hstep6 : ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m)
    (hstep7 : ∠ f:k:h + ∠ k:h:g = ∟ + ∟) :
    ∠ k:h:g + ∠ g:h:m = ∟ + ∟ := by
  euclid_finish

end Elements.Book1
