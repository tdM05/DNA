import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step8 (ABC CDE : Circle)
    (habsurd : ¬(∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE)) :
    ¬(∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE) := by
  exact habsurd

end Elements.Book3
