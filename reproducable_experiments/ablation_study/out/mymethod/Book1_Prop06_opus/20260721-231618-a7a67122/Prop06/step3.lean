import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step3
  (a b c d : Point)
  (hbet : between b d a) (hbd : |(b─d)| = |(a─c)|) :
    between b d a ∧ |(b─d)| = |(a─c)| := by
  exact ⟨hbet, hbd⟩

end Elements.Book1
