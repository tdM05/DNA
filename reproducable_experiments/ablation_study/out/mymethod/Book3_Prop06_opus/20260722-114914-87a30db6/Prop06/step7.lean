import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step7 (f c : Point) (ABC CDE : Circle)
    (hne : ABC ≠ CDE)
    (hfABC : f.isCentre ABC) (hfCDE : f.isCentre CDE)
    (hcABC : c.onCircle ABC) (hcCDE : c.onCircle CDE) :
    False := by
  euclid_apply (equal_circles f c c ABC CDE)
  euclid_finish

end Elements.Book3
