import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step5
  (a b c d : Point)
  (hlen : |(b─d)| = |(a─c)|)
  : |(d─b)| = |(a─c)| ∧ |(b─c)| = |(c─b)| := by
  euclid_finish

end Elements.Book1
