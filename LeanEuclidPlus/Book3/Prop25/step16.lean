import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step16 (a b c : Point) (α : Circle)
    (haC : a.onCircle α) (hstep15 : b.onCircle α ∧ c.onCircle α) :
    a.onCircle α ∧ b.onCircle α ∧ c.onCircle α := by
  euclid_finish

end Elements.Book3
