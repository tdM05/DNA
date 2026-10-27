import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step7
  (b g : Point) (AE FD EF : Line)
  (step1 : g.sameSide b EF ∨ g.opposingSides b EF)
  (hassump1 : ¬(g.sameSide b EF) ∧ ¬(g.opposingSides b EF))
  : ¬(AE.intersectsLine FD) := by
  rcases step1 with h | h
  · exact absurd h hassump1.1
  · exact absurd h hassump1.2

end Elements.Book1
