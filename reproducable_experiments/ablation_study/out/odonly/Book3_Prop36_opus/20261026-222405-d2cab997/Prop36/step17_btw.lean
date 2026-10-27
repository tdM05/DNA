import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_btw (a c f : Point) (ABC : Circle) (DA : Line)
    (hada : a.onLine DA) (hcda : c.onLine DA) (hfDA : f.onLine DA)
    (hacirc : a.onCircle ABC) (hccirc : c.onCircle ABC)
    (hfin : f.insideCircle ABC) (hac : a ≠ c) :
    between a f c := by
  euclid_finish

end Elements.Book3
