import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hbα₃ (a b e : Point) (α₃ : Circle)
    (he_centre : e.isCentre α₃) (ha_circ : a.onCircle α₃)
    (hEb : |(e─a)| = |(e─b)|) :
    b.onCircle α₃ := by
  euclid_finish

end Elements.Book3
