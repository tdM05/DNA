import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step3 (a c d d' : Point) (AB AC DC : Line)
    (hdDC : d.onLine DC) (hcDC : c.onLine DC)
    (haAB : a.onLine AB) (hd'AB : d'.onLine AB) (hadd' : between a d d')
    (hcAC : c.onLine AC) (haAC : a.onLine AC) (hACAB : AC ≠ AB) :
    distinctPointsOnLine d c DC := by
  euclid_finish

end Elements.Book1
