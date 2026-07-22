import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step1 (a b c : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(a─b)| ≠ |(a─c)|)   -- "$AB$ is unequal to $AC$"
  : |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)| := by
  rcases lt_or_gt_of_ne hassump1 with h | h
  · exact Or.inr h
  · exact Or.inl h

end Elements.Book1
