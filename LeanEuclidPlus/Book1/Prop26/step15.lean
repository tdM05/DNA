import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step15 (a b c d e f : Point)
    (step13 : |(a─b)| = |(d─e)|) (step14 : |(b─c)| = |(e─f)|) :
    |(a─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)| := ⟨step13, step14⟩

end Elements.Book1
