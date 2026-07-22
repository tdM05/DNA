import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hcα₂ (a b c d : Point) (α₂ : Circle)
    (hdc : d.isCentre α₂) (ha : a.onCircle α₂)
    (hdab : |(d─a)| = |(d─b)|) (hdbc : |(d─b)| = |(d─c)|) :
    c.onCircle α₂ := by
  euclid_apply (point_on_circle_if d a c α₂)
  euclid_finish

end Elements.Book3
