import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step2
  (a b c : Point)
  (hgt : |(a─b)| > |(a─c)|)
  : |(a─b)| > |(a─c)| := by
  exact hgt

end Elements.Book1
