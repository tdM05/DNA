import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step3 (a b : Point) (AC AB : Line)
    (hAC_a : a.onLine AC) (hb_off : ¬b.onLine AC)
    (hAB_a : a.onLine AB) (hAB_b : b.onLine AB) :
    distinctPointsOnLine a b AB := by
  euclid_finish

end Elements.Book3
