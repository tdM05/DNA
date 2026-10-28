import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_3_step2 (a d : Point) (DEF : Circle)
    (h_centre : a.isCentre DEF) (h_on : d.onCircle DEF) :
    a.isCentre DEF ∧ d.onCircle DEF := by
  exact ⟨h_centre, h_on⟩

end Elements.Book1
