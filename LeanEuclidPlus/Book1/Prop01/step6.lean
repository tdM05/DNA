import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_1_step6 (a b c : Point)
  (step4 : |(a─c)| = |(a─b)|)
  : |(c─a)| = |(a─b)| := by euclid_finish

end Elements.Book1
