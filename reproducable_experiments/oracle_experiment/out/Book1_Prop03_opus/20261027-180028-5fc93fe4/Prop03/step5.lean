import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_3_step5 (a d e c₀ c₁ : Point)
    (step3 : |(a─e)| = |(a─d)|) (step4 : |(c₀─c₁)| = |(a─d)|) :
    |(a─e)| = |(a─d)| ∧ |(c₀─c₁)| = |(a─d)| := by
  exact ⟨step3, step4⟩

end Elements.Book1
