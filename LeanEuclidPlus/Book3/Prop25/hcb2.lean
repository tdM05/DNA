import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hcb2 (a b d : Point) (α : Circle)
    (hcentre : d.isCentre α) (haC : a.onCircle α) (heq : |(d─a)| = |(d─b)|) : b.onCircle α := by
  euclid_apply (point_on_circle_if d a b α)
  euclid_finish

end Elements.Book3
