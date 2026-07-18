import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step3 (b c d e f g : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(b─g)| = |(d─e)|)   -- "$BG$ is equal to $DE$"
  (hassump2 : |(b─c)| = |(e─f)|)   -- "$BC$ to $EF$"
  : |(g─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)| := by
  euclid_finish

end Elements.Book1
