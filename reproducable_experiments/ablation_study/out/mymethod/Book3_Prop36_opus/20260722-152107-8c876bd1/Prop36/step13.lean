import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step13 (e : Point) (ABC : Circle)
  (h : e.isCentre ABC)
  : e.isCentre ABC := by
  exact h

end Elements.Book3
