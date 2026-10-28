import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_25_step10 (a c d e : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(a─d)| = |(d─c)|)   -- "$AD$ is equal to $DC$"
  (hassump2 : |(d─e)| = |(d─e)|)   -- "$DE$ (is) common"
  : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)| := by
  euclid_finish

end Elements.Book3
