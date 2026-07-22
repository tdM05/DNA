import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step1 (a b d : Point) (AB AD DB : Line)
    (hb : b.onLine DB) (hd : d.onLine DB)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hab : a ≠ b) (hADAB : AD ≠ AB) :
    distinctPointsOnLine d b DB := by
  euclid_finish

end Elements.Book1
