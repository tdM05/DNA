import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hec (a b c d e : Point) (AC DB : Line)
    (heDB : e.onLine DB) (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (hcAC : c.onLine AC) (haAC : a.onLine AC) (hboff : ¬ b.onLine AC)
    (hbtw : between a d c) :
    e ≠ c := by
  euclid_finish

end Elements.Book3
