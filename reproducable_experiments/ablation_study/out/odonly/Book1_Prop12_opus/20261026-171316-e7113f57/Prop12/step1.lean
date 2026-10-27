import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step1 (c d : Point) (AB : Line)
    (hd : ¬d.onLine AB) (hc : ¬c.onLine AB) (hns : ¬d.sameSide c AB) :
    d.opposingSides c AB := by
  euclid_finish

end Elements.Book1
