import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_42_s6_x2 (b e c : Point) (BC : Line)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_bet : between b e c) :
    e.onLine BC := by
  euclid_finish

end Elements.Book1
