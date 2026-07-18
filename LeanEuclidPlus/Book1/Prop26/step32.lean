import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step32 (a b c d e f : Point)
    (h_ang2 : ∠ b:c:a = ∠ e:f:d) :
    ∠ e:f:d = ∠ b:c:a := h_ang2.symm

end Elements.Book1
