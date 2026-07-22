import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_haα₂ (a : Point) (α₂ : Circle)
    (ha : a.onCircle α₂) : a.onCircle α₂ := ha

end Elements.Book3
