import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step13 (f g h l m : Point)
    (hstep12 : ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l) :
    ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l := by
  euclid_finish

end Elements.Book1
