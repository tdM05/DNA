import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_31_s4 (e a f : Point)
    (hbetween : between e a f) : between e a f := by
  exact hbetween

end Elements.Book1
