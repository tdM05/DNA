import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step2 (a b d : Point) (AB AD BD : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hab : a ≠ b)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD) (hang : ∠ b:a:d = ∟)
    (hb_bd : b.onLine BD) (hd_bd : d.onLine BD) :
    distinctPointsOnLine b d BD := by
  euclid_finish

end Elements.Book2
