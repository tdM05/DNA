import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_41_s1 (a b c : Point) (CD AC : Line)
    (h_a_on : a.onLine AC) (h_c_on : c.onLine AC)
    (h_c_CD : c.onLine CD)
    (h_sameSide : a.sameSide b CD) : distinctPointsOnLine a c AC := by
  euclid_finish

end Elements.Book1
