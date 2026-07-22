import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step5 (a g d : Point) (ADE : Circle)
    (h_gc : g.isCentre ADE) (h_aADE : a.onCircle ADE) (h_dADE : d.onCircle ADE) :
    |(a─g)| = |(g─d)| := by
  euclid_finish

end Elements.Book3
