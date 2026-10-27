import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_bet (a c d f : Point) (ABC : Circle) (DA : Line)
  (haC : a.onCircle ABC) (hcC : c.onCircle ABC)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA)
  (hdca : between d c a)
  (hfin : f.insideCircle ABC) :
    between a f c := by euclid_finish

end Elements.Book3
