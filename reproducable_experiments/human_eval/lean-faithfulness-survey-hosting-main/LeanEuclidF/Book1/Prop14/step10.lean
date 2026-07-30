import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_14_s10 (BC BD : Line) (habsurd : ¬ BC ≠ BD) : BC = BD := by
  by_contra h
  exact habsurd h

end Elements.Book1
