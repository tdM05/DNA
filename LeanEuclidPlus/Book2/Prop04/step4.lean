import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step4 (g : Point) (HK AB : Line)
    (hg_hk : g.onLine HK) (hhk_ab : ¬(HK.intersectsLine AB)) :
    g.onLine HK ∧ ¬(HK.intersectsLine AB) :=
  ⟨hg_hk, hhk_ab⟩

end Elements.Book2
