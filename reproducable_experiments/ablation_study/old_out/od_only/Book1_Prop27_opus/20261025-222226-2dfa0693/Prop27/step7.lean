import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step7
    (b g : Point) (AE FD EF : Line)
    (hdisj : g.sameSide b EF ∨ g.opposingSides b EF)
    (hneither : ¬(g.sameSide b EF) ∧ ¬(g.opposingSides b EF)) :
    ¬(AE.intersectsLine FD) := by
  euclid_finish

end Elements.Book1
