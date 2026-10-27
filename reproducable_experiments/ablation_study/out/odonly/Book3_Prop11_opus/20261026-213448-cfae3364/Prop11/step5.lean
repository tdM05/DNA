import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step5 (a g d : Point) (ADE : Circle)
    (hg_centre : g.isCentre ADE) (ha_ADE : a.onCircle ADE) (hd_ADE : d.onCircle ADE) :
    |(a─g)| = |(g─d)| := by
  euclid_finish

end Elements.Book3
