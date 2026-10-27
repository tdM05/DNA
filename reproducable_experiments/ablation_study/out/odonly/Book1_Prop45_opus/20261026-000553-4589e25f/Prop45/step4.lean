import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step4 (e₁ e₂ e₃ f g h k m : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ e₁:e₂:e₃ = ∠ h:k:f ∧ ∠ e₁:e₂:e₃ = ∠ g:h:m)   -- "angle $E$ is equal to each of (angles) $HKF$ and $GHM$"
  : ∠ h:k:f = ∠ g:h:m := by
  euclid_finish

end Elements.Book1
