import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- TODO: fill object/hypothesis binders (run --context step4)
theorem helper_3_36_step4
  (a c d f : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(a─f)| = |(f─c)|)   -- "straight-line $AC$ is cut in half at $F$"
  : |(a─f)| + |(c─d)| = |(f─c)| + |(c─d)| := by
  rw [hassump1]

end Elements.Book3
