import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step11 (a c d e : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟)   -- "For each (is) a right-angle"
  : ∠ a:d:e = ∠ c:d:e := by
  rw [hassump1.1, hassump1.2]

end Elements.Book3
