import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_11_s1 (a c d : Point) (h : between c d a) : between a d c := by
  euclid_finish

end Elements.Book1
