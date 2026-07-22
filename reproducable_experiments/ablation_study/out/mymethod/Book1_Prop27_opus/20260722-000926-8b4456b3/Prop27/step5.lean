import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step5
  (g b : Point) (EF : Line)
  (h_nbd : ¬(g.sameSide b EF))
  : ¬(g.sameSide b EF) := h_nbd

end Elements.Book1
