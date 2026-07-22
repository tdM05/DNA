import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step24_df
  (a c d f : Point) (DA : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA)
  (hbdca : between d c a)
  (step17 : |(a─f)| = |(f─c)|)
  : d ≠ f := by euclid_finish

end Elements.Book3
