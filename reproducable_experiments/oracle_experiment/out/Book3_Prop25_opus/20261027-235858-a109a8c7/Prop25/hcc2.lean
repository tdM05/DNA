import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_25_hcc2 (a c d : Point) (α : Circle)
    (hcentre : d.isCentre α) (haC : a.onCircle α) (heq : |(a─d)| = |(d─c)|) : c.onCircle α := by
  euclid_apply (point_on_circle_if d a c α)
  euclid_finish

end Elements.Book3
