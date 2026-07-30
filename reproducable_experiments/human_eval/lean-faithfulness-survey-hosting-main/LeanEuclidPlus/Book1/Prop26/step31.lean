import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_26_s31
    (hstep30 : ∠ b:a:h = ∠ e:d:f ∧ ∠ b:h:a = ∠ e:f:d) :
    ∠ b:h:a = ∠ e:f:d :=
  hstep30.2

end Elements.Book1
