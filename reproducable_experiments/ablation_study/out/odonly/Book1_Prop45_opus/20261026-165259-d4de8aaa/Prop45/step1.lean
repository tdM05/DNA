import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step1 (a b d : Point) (AB AD DB : Line)
  (hbDB : b.onLine DB) (hdDB : d.onLine DB)
  (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
  (hdAD : d.onLine AD) (haAD : a.onLine AD) (hADAB : AD ≠ AB)
  : distinctPointsOnLine d b DB := by euclid_finish

end Elements.Book1
