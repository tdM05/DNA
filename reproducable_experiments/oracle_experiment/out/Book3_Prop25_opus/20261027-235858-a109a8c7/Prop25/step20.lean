import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_25_step20 (a c d : Point) (AC : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hadc : between a d c) : d.onLine AC := by
  euclid_finish

end Elements.Book3
