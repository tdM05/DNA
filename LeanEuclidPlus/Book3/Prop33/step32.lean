import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step32
    (g b : Point) (GB : Line)
    (h_g_GB : g.onLine GB) (h_b_GB : b.onLine GB) (h_gb : g ≠ b) :
    distinctPointsOnLine g b GB := by
  euclid_finish

end Elements.Book3
