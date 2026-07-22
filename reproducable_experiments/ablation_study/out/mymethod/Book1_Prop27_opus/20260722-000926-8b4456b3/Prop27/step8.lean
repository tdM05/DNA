import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step8
  (AE FD : Line)
  (step7 : ¬(AE.intersectsLine FD))
  : ¬(AE.intersectsLine FD) := step7

end Elements.Book1
