import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step8 (b c d e f g : Point)
    (step7 : ∠ b:g:c = ∠ e:d:f ∧ ∠ g:c:b = ∠ d:f:e) :
    ∠ g:c:b = ∠ d:f:e := step7.2

end Elements.Book1
