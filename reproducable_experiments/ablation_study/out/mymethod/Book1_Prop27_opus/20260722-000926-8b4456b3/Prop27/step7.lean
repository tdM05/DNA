import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step7
  (b g : Point) (AE FD EF : Line)
  (h_or : g.sameSide b EF ∨ g.opposingSides b EF)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ¬(g.sameSide b EF) ∧ ¬(g.opposingSides b EF))   -- "meeting in neither direction"
  : ¬(AE.intersectsLine FD) := by
  exfalso
  rcases h_or with h | h
  · exact hassump1.1 h
  · exact hassump1.2 h

end Elements.Book1
