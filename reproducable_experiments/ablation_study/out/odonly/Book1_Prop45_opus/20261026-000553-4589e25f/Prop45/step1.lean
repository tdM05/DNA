import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step1 (a b d : Point) (AB AD DB : Line)
    (h_ab_a : a.onLine AB) (h_ab_b : b.onLine AB)
    (h_ad_a : a.onLine AD) (h_ad_d : d.onLine AD)
    (h_db_b : b.onLine DB) (h_db_d : d.onLine DB)
    (h_ab : a ≠ b) (h_ADAB : AD ≠ AB) : distinctPointsOnLine d b DB := by
  euclid_finish

end Elements.Book1
