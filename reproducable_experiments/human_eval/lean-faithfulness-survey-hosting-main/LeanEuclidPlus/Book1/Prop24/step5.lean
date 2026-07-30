import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_24_s5
  (h_s1 : ∠ e:d:g = ∠ b:a:c)
  : ∠ b:a:c = ∠ e:d:g := h_s1.symm

end Elements.Book1
