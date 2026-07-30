import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_27_s8
  (AE FD : Line)
  (s7 : ¬AE.intersectsLine FD)
  : ¬AE.intersectsLine FD :=
  s7

end Elements.Book1
