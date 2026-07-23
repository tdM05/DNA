import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step6
  (b c f : Point) (ABC : Circle)
  (hb_circ : b.onCircle ABC) (hc_circ : c.onCircle ABC) (hfcenter : f.isCentre ABC)
  : |(f─c)| = |(f─b)| := by
  euclid_finish

end Elements.Book3
