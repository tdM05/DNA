import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hcα₂ (a b c d : Point) (α₂ : Circle)
    (hd_centre : d.isCentre α₂) (ha_circ : a.onCircle α₂)
    (hstep19a : |(d─a)| = |(d─b)|) (hstep19b : |(d─b)| = |(d─c)|) :
    c.onCircle α₂ := by
  -- DC = DA, so C is on the circle centred at D through A
  euclid_finish

end Elements.Book3
