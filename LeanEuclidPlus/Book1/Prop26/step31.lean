import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step31 (a b d e f h : Point)
    (step30 : ∠ b:a:h = ∠ e:d:f ∧ ∠ b:h:a = ∠ e:f:d) :
    ∠ b:h:a = ∠ e:f:d := step30.2

end Elements.Book1
