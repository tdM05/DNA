import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_1_step2 (a b : Point) (ACE : Circle)
    (hcentre : b.isCentre ACE) (honcircle : a.onCircle ACE) :
    b.isCentre ACE ∧ a.onCircle ACE := by
  exact ⟨hcentre, honcircle⟩

end Elements.Book1
