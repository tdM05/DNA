import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hcα₂ (a c d : Point) (α₂ : Circle)
    (hcentre : d.isCentre α₂) (ha_circ : a.onCircle α₂)
    (hmid : |(a─d)| = |(d─c)|) :
    c.onCircle α₂ := by
  euclid_finish

end Elements.Book3
