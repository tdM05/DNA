import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_26_s13
    (hstep12 : ¬|(a─b)| ≠ |(d─e)|) :
    |(a─b)| = |(d─e)| :=
  Classical.not_not.mp hstep12

end Elements.Book1
