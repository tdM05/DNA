import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step33 (a b c e f h : Point)
    (step31 : ∠ b:h:a = ∠ e:f:d) (step32 : ∠ e:f:d = ∠ b:c:a) :
    ∠ b:h:a = ∠ b:c:a := step31.trans step32

end Elements.Book1
