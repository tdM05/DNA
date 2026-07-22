import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hec (a b c d e : Point) (AC DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hboff : ¬b.onLine AC)
    (hadc : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB) :
    e ≠ c := by
  euclid_finish

end Elements.Book3
