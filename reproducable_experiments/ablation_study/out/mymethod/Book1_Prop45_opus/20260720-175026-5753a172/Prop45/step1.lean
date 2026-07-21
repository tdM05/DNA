import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step1
    (a b d : Point) (AB AD DB : Line)
    (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab : a ≠ b)
    (had_a : a.onLine AD) (had_d : d.onLine AD) (hADAB : AD ≠ AB)
    (hdb_b : b.onLine DB) (hdb_d : d.onLine DB) :
    distinctPointsOnLine d b DB := by
  euclid_finish

end Elements.Book1
