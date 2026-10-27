import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step23_tri (c e f : Point) (DA EF EC : Line)
  (hfDA : f.onLine DA) (hcDA : c.onLine DA)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  (heEC : e.onLine EC) (hcEC : c.onLine EC)
  (henef : e ≠ f) (hfnec : f ≠ c) (heoff : ¬ e.onLine DA) :
    formTriangle f e c EF EC DA := by euclid_finish

end Elements.Book3
