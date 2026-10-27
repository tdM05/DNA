import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step26 (b c e : Point) (ABC : Circle)
  (he : e.isCentre ABC) (hcC : c.onCircle ABC) (hbC : b.onCircle ABC) :
    |(e─c)| = |(e─b)| := by euclid_finish

end Elements.Book3
