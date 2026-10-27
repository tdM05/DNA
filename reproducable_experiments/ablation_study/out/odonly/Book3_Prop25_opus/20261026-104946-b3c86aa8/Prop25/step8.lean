import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step8 (c e : Point) (EC : Line)
    (he_EC : e.onLine EC) (hc_EC : c.onLine EC) (hec : e ≠ c) :
    distinctPointsOnLine e c EC := by
  euclid_finish

end Elements.Book3
