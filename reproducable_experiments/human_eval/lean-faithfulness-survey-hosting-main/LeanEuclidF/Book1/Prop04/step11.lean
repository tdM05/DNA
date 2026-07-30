import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_4_s11
  (s9 : ∠ a:b:c = ∠ d:e:f ∧ ∠ a:c:b = ∠ d:f:e)
  : ∠ a:c:b = ∠ d:f:e :=
  s9.2

end Elements.Book1
