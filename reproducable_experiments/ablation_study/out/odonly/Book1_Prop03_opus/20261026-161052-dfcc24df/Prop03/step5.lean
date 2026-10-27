import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_3_step5
  (a c₀ c₁ d e : Point)
  (hstep3 : |(a─e)| = |(a─d)|)
  (hstep4 : |(c₀─c₁)| = |(a─d)|)
  : |(a─e)| = |(a─d)| ∧ |(c₀─c₁)| = |(a─d)| := by
  exact ⟨hstep3, hstep4⟩

end Elements.Book1
