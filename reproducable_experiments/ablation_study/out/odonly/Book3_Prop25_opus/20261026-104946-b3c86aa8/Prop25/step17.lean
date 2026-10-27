import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step17 (a b c e : Point) (α₁ : Circle)
    (hstep16 : e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁) :
    a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  exact ⟨hstep16.2.1, hstep16.2.2.1, hstep16.2.2.2⟩

end Elements.Book3
