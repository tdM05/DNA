import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_1_step9 (a b c : Point)
  (step7 : |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|)
  (step8 : (|(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|) → |(c─a)| = |(c─b)|)
  : |(c─a)| = |(c─b)| := by
  exact step8 step7

end Elements.Book1
