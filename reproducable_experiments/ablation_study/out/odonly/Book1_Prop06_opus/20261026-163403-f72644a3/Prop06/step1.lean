import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step1 (a b c : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(a─b)| ≠ |(a─c)|)   -- "$AB$ is unequal to $AC$"
  : |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)| := by
  rcases hassump1.lt_or_lt with h | h
  · right; exact h
  · left; exact h

end Elements.Book1
