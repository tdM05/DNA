import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step37 (a b d e : Point)
    (step19 : |(a─b)| = |(d─e)|) :
    |(a─b)| = |(d─e)| := step19

end Elements.Book1
