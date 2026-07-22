import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step5 (a b d : Point)
    (hgt : ∠ a:b:d > ∠ b:a:d) :
    ∠ a:b:d > ∠ b:a:d := hgt

end Elements.Book3
