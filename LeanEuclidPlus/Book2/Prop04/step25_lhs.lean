import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step25_lhs (a c g h : Point) (AB CF AD HK : Line)
    (hacgh : formParallelogram a c h g AB HK AD CF)
    : Triangle.area △ a:c:g + Triangle.area △ a:g:h = Triangle.area △ c:a:h + Triangle.area △ c:h:g := by
  euclid_apply (parallelogram_area a c h g AB HK AD CF)
  euclid_finish

end Elements.Book2
