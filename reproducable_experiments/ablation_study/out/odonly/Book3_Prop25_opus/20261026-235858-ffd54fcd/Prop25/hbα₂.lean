import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hbα₂ (a b d : Point) (α₂ : Circle)
    (hd_centre : d.isCentre α₂) (ha_circ : a.onCircle α₂)
    (hstep19a : |(d─a)| = |(d─b)|) :
    b.onCircle α₂ := by
  -- DB = DA, so B is on the circle centred at D through A
  euclid_finish

end Elements.Book3
