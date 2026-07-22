import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step23_tri
  (a c d e f : Point) (ABC : Circle) (DA EC EF : Line)
  (hc : c.onCircle ABC)
  (hfDA : f.onLine DA) (hcDA : c.onLine DA)
  (hcEC : c.onLine EC) (heEC : e.onLine EC)
  (hfEF : f.onLine EF) (heEF : e.onLine EF)
  (hnotDA : ¬ e.onLine DA)
  (step13 : e.isCentre ABC)
  (step17 : |(a─f)| = |(f─c)|)
  (hbdca : between d c a)
  : formTriangle f c e DA EC EF := by euclid_finish

end Elements.Book3
