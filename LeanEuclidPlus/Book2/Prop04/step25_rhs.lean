import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step25_rhs (e f g k : Point) (HK DE CF BE : Line)
    (hgkef : formParallelogram g k f e HK DE CF BE)
    : Triangle.area △ g:k:e + Triangle.area △ g:e:f = Triangle.area △ k:g:f + Triangle.area △ k:f:e := by
  euclid_apply (parallelogram_area g k f e HK DE CF BE)
  euclid_finish

end Elements.Book2
