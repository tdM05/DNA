import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_6_step10 (a b c : Point)
    (habsurd1 : ¬(|(a─b)| ≠ |(a─c)|)) :
    ¬(|(a─b)| ≠ |(a─c)|) := by
  exact habsurd1

end Elements.Book1
