import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step9 (e g h : Point) (AB : Line)
    (heAB : e.onLine AB) (hgAB : g.onLine AB) (hbet : between e h g) :
    h.onLine AB := by
  euclid_finish

end Elements.Book1
