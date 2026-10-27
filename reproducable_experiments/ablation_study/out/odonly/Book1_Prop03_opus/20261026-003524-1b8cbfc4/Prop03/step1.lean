import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_3_step1 (a d c₀ c₁ : Point)
    (h : |(a─d)| = |(c₀─c₁)|) : |(a─d)| = |(c₀─c₁)| := by
  exact h

end Elements.Book1
