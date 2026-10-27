import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step8
    (AE FD : Line)
    (hpar : ¬(AE.intersectsLine FD)) :
    ¬(AE.intersectsLine FD) := by
  euclid_finish

end Elements.Book1
