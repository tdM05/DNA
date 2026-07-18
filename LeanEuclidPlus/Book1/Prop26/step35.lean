import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step35 (b c e f : Point)
    (habsurd2 : ¬(|(b─c)| ≠ |(e─f)|)) :
    ¬(|(b─c)| ≠ |(e─f)|) := habsurd2

end Elements.Book1
