import SystemE
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step6 (f c e b : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(f─c)| = |(f─b)|)   -- "$FC$ was shown (to be) equal to $FB$"
  (hce : |(f─c)| = |(f─e)|)
  : |(f─e)| = |(f─b)| := by
  linarith

end Elements.Book3
