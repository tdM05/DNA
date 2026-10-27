import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_haα₃ (a : Point) (α₃ : Circle) (ha_circ : a.onCircle α₃) :
    a.onCircle α₃ := by
  exact ha_circ

end Elements.Book3
