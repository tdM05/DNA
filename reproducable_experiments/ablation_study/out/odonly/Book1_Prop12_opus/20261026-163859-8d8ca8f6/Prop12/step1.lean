import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step1 (c d : Point) (AB : Line)
    (h1 : ¬d.onLine AB) (h2 : ¬c.onLine AB) (h3 : ¬d.sameSide c AB) :
    d.opposingSides c AB := by
  euclid_finish

end Elements.Book1
