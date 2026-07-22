import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step23_cDA
  (a c d : Point) (DA : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA)
  (hbdca : between d c a)
  : c.onLine DA := by euclid_finish

end Elements.Book3
