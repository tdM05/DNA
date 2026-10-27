import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step24_tri (d e f : Point) (DA EF ED : Line)
  (hfDA : f.onLine DA) (hdDA : d.onLine DA)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  (heED : e.onLine ED) (hdED : d.onLine ED)
  (henef : e ≠ f) (hdnef : d ≠ f) (heoff : ¬ e.onLine DA) :
    formTriangle f d e DA ED EF := by euclid_finish

end Elements.Book3
