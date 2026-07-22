import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step1 (a b d : Point) (AB AD DB : Line)
    (hbDB : b.onLine DB) (hdDB : d.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hABAD : AD ≠ AB) (hab : a ≠ b) :
    distinctPointsOnLine d b DB := by
  euclid_finish

end Elements.Book1
