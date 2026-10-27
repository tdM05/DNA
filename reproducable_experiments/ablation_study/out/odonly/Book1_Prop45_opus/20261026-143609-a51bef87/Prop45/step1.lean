import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step1 (a b d : Point) (AB AD DB : Line)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
    (hd_AD : d.onLine AD) (ha_AD : a.onLine AD)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hab : a ≠ b) (hADAB : AD ≠ AB) :
    distinctPointsOnLine d b DB := by
  euclid_finish

end Elements.Book1
