import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step26 (a b d e f h : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(b─h)| = |(e─f)|)   -- "$BH$ is equal to $EF$"
  (hassump2 : |(a─b)| = |(d─e)|)   -- "$AB$ to $DE$"
  : |(a─b)| = |(d─e)| ∧ |(b─h)| = |(e─f)| := ⟨hassump2, hassump1⟩

end Elements.Book1
