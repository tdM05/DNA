import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step12
    (e b : Point) (EB : Line)
    (h_e_EB : e.onLine EB) (h_b_EB : b.onLine EB) (h_eb : e ≠ b) :
    distinctPointsOnLine e b EB := by
  euclid_finish

end Elements.Book3
