import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hca2 (a : Point) (α : Circle) (haC : a.onCircle α) : a.onCircle α := by
  exact haC

end Elements.Book3
