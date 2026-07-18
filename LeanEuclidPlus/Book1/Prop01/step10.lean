import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_1_step10 (a b c : Point)
  (step6 : |(c─a)| = |(a─b)|)
  (step5 : |(b─c)| = |(b─a)|)
  : |(c─a)| = |(a─b)| ∧ |(a─b)| = |(b─c)| := by euclid_finish

end Elements.Book1
