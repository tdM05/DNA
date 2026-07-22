import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step2 (c d : Point) (EFG : Circle)
    (h1 : c.isCentre EFG) (h2 : d.onCircle EFG) :
    c.isCentre EFG ∧ d.onCircle EFG := by
  exact ⟨h1, h2⟩

end Elements.Book1
