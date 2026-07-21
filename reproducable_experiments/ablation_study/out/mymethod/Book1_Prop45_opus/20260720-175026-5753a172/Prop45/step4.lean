import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step4
  (e₁ e₂ e₃ f g h k m : Point)
  (hassump1 : ∠ e₁:e₂:e₃ = ∠ h:k:f ∧ ∠ e₁:e₂:e₃ = ∠ g:h:m)
  : ∠ h:k:f = ∠ g:h:m := by
  obtain ⟨h1, h2⟩ := hassump1
  rw [← h1, h2]

end Elements.Book1
