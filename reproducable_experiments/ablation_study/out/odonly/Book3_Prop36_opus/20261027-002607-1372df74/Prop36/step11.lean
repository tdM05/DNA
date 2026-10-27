import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step11
  (a b c d : Point)
  (step10 : |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)|)
  : |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)| := by
  exact step10

end Elements.Book3
