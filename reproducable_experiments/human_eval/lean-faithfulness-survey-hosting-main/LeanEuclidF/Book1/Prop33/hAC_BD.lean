import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_33_x1
  (a b c : Point) (AC BD : Line)
  (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC) (h_ac : a ≠ c)
  (h_b_BD : b.onLine BD)
  (h_same : a.sameSide c BD)
  : AC ≠ BD := by
  euclid_finish

end Elements.Book1
