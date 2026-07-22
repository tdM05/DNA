import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step21 (a c d : Point) (α₂ : Circle)
    (hadc : between a d c) (hdc : d.isCentre α₂) :
    between a d c ∧ d.isCentre α₂ := ⟨hadc, hdc⟩

end Elements.Book3
