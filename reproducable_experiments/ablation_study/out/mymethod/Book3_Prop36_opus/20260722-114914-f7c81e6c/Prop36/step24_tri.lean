import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step24_tri
  (d e f : Point) (DA ED EF : Line)
  (hfDA : f.onLine DA) (hdDA : d.onLine DA)
  (hdED : d.onLine ED) (heED : e.onLine ED)
  (hfEF : f.onLine EF) (heEF : e.onLine EF)
  (hnotDA : ¬ e.onLine DA)
  (step24_df : d ≠ f)
  : formTriangle f d e DA ED EF := by euclid_finish

end Elements.Book3
