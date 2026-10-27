import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step26
  (b c e : Point) (ABC : Circle)
  (hb : b.onCircle ABC) (hc : c.onCircle ABC)
  (he : e.isCentre ABC)
  : |(e─c)| = |(e─b)| := by
  euclid_finish

end Elements.Book3
