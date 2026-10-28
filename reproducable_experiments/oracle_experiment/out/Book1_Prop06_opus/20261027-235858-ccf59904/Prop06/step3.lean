import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_6_step3 (a b c d : Point)
    (hbd : |(b─d)| = |(a─c)|) :
    |(d─b)| = |(a─c)| := by
  euclid_finish

end Elements.Book1
