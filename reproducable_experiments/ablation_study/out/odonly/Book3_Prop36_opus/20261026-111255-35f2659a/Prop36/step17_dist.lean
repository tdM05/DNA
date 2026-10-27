import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_dist (a c d : Point) (DA : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hdca : between d c a) :
    distinctPointsOnLine a c DA := by euclid_finish

end Elements.Book3
