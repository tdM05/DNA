import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step7
  (b g : Point) (AE FD EF : Line)
  (step1 : g.sameSide b EF ∨ g.opposingSides b EF)
  (hassump1 : ¬(g.sameSide b EF) ∧ ¬(g.opposingSides b EF))
  : ¬(AE.intersectsLine FD) := by
  exfalso
  rcases step1 with h | h
  · exact hassump1.1 h
  · exact hassump1.2 h

end Elements.Book1
