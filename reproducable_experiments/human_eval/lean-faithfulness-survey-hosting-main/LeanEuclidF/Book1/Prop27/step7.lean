import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_27_s7
  (g b : Point) (AE FD EF : Line)
  (s1 : g.sameSide b EF ∨ g.opposingSides b EF)
  (hassump1 : ¬(g.sameSide b EF) ∧ ¬(g.opposingSides b EF))
  : ¬(AE.intersectsLine FD) :=
  fun _ => s1.elim (absurd · hassump1.1) (absurd · hassump1.2)

end Elements.Book1
