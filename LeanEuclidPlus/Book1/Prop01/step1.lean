import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_1_step1 (a b : Point) (BCD : Circle)
    (hcentre : a.isCentre BCD) (honcircle : b.onCircle BCD) :
    a.isCentre BCD ∧ b.onCircle BCD := by
  exact ⟨hcentre, honcircle⟩

end Elements.Book1
