import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step5 (a g d : Point) (ADE : Circle)
  (ha_ADE : a.onCircle ADE) (hd_ADE : d.onCircle ADE)
  (hg_c : g.isCentre ADE)
  : |(a─g)| = |(g─d)| := by
  euclid_finish

end Elements.Book3
