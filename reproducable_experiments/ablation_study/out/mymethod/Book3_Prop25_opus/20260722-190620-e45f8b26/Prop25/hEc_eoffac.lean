import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hEc_eoffac (b e : Point) (AC : Line)
    (hbse : b.sameSide e AC) :
    ¬ e.onLine AC := by
  euclid_finish

end Elements.Book3
