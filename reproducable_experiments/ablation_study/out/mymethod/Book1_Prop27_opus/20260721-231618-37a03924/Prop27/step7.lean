import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step7
  (b g : Point) (AE FD EF : Line)
  (step1 : g.sameSide b EF ∨ g.opposingSides b EF)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ¬(g.sameSide b EF) ∧ ¬(g.opposingSides b EF))   -- "meeting in neither direction"
  : ¬(AE.intersectsLine FD) := by
  obtain ⟨hns, hno⟩ := hassump1
  rcases step1 with h | h
  · exact absurd h hns
  · exact absurd h hno

end Elements.Book1
