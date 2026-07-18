import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step36 (b c e f : Point)
    (step35 : ¬(|(b─c)| ≠ |(e─f)|)) :
    |(b─c)| = |(e─f)| := by
  by_contra h
  exact step35 h

end Elements.Book1
