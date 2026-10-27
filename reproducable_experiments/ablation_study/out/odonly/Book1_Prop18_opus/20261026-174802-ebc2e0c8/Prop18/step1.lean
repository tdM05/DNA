import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step1 (a b d : Point)
  (heq : |(a─d)| = |(a─b)|) : |(a─d)| = |(a─b)| := by
  exact heq

end Elements.Book1
