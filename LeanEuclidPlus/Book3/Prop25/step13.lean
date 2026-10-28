import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step13 (a b c e : Point)
  (hstep12 : |(a─e)| = |(c─e)|)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(a─e)| = |(b─e)|)   -- "$AE$ was shown (to be) equal to $BE$"
  : |(b─e)| = |(c─e)| := by
  euclid_finish

end Elements.Book3
