import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_3_step6 (a e d c₀ c₁ : Point)
    (step5 : |(a─e)| = |(a─d)| ∧ |(c₀─c₁)| = |(a─d)|)
    : |(a─e)| = |(c₀─c₁)| := by
  exact step5.1.trans step5.2.symm

end Elements.Book1
