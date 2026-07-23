import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step3 (a b : Point) (AC AB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haAC : a.onLine AC) (hboff : ¬b.onLine AC) :
    distinctPointsOnLine a b AB := by
  euclid_finish

end Elements.Book3
