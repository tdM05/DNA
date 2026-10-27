import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step1 (ABC CDE : Circle) (f : Point)
    (hfABC : f.isCentre ABC) (hfCDE : f.isCentre CDE) :
    f.isCentre ABC ∧ f.isCentre CDE := by
  exact ⟨hfABC, hfCDE⟩

end Elements.Book3
