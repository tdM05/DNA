import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step3
    (a b c d d' : Point)
    (AB BC AC DC : Line)
    (ha : a.onLine AB)
    (hb : b.onLine AB)
    (hab : a ≠ b)
    (hd' : d'.onLine AB)
    (hbBC : b.onLine BC)
    (hcBC : c.onLine BC)
    (hcAC : c.onLine AC)
    (haAC : a.onLine AC)
    (hABBC : AB ≠ BC)
    (hBCAC : BC ≠ AC)
    (hACAB : AC ≠ AB)
    (hadd' : between a d d')
    (hdDC : d.onLine DC)
    (hcDC : c.onLine DC) :
    distinctPointsOnLine d c DC := by euclid_finish

end Elements.Book1
