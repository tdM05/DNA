import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step20 (d : Point) (α₂ : Circle)
    (hdc : d.isCentre α₂) : d.isCentre α₂ := hdc

end Elements.Book3
