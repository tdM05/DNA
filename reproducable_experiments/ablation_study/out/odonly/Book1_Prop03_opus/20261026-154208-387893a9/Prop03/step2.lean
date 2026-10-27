import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_3_step2 (a d : Point) (DEF : Circle)
    (hc : a.isCentre DEF) (ho : d.onCircle DEF) : a.isCentre DEF ∧ d.onCircle DEF := by
  exact ⟨hc, ho⟩

end Elements.Book1
