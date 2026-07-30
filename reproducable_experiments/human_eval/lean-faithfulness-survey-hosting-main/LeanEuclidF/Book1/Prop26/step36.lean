import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_26_s36
    (hstep35 : ¬(|(b─c)| ≠ |(e─f)|)) :
    |(b─c)| = |(e─f)| :=
  Classical.not_not.mp hstep35

end Elements.Book1
