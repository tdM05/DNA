import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step4
  (a f c d : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(a─f)| = |(f─c)|)   -- "straight-line $AC$ is cut in half at $F$"
  : |(a─f)| + |(c─d)| = |(f─c)| + |(c─d)| := by
  rw [hassump1]

end Elements.Book3
