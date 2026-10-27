import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step3 (AH BG : Line) (hpar : ¬(AH.intersectsLine BG)) :
    ¬(BG.intersectsLine AH) := by
  intro hc
  exact hpar (intersection_symm BG AH hc)

end Elements.Book1
