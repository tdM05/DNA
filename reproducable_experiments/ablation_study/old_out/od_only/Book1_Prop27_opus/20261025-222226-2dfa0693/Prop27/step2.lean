import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step2
    (b g : Point) (AE FD EF : Line)
    (hgAE : g.onLine AE) (hgFD : g.onLine FD) (hgsb : g.sameSide b EF) :
    g.onLine AE ∧ g.onLine FD ∧ g.sameSide b EF := by
  euclid_finish

end Elements.Book1
