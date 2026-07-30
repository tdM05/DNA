import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_23_s1 (d e : Point) (CE DE : Line)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (he_CE : e.onLine CE) (hd_notCE : ¬d.onLine CE)
    : distinctPointsOnLine d e DE := by
  euclid_finish

end Elements.Book1
