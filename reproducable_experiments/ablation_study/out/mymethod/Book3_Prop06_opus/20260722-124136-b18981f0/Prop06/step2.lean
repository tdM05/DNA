import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step2 (FC : Line) (f c : Point)
    (hf : f.onLine FC) (hc : c.onLine FC) :
    f.onLine FC ∧ c.onLine FC := by
  exact ⟨hf, hc⟩

end Elements.Book3
