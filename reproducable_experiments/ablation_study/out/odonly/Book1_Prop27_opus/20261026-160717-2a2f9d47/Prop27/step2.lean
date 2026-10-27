import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step2
  (b g : Point) (AE FD EF : Line)
  (h_g_AE : g.onLine AE) (h_g_FD : g.onLine FD) (hbd : g.sameSide b EF)
  : g.onLine AE ∧ g.onLine FD ∧ g.sameSide b EF := by
  exact ⟨h_g_AE, h_g_FD, hbd⟩

end Elements.Book1
