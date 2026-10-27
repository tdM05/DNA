import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout_out (a g astar : Point) (ADE : Circle)
  (ha_ADE : a.onCircle ADE) (hg_c : g.isCentre ADE)
  (hgt : |(g─astar)| > |(g─a)|)
  : astar.outsideCircle ADE := by
  euclid_finish

end Elements.Book3
