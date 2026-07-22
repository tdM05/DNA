import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step7 (ABC CDE : Circle) (f b e : Point)
    (hfABC : f.isCentre ABC) (hfCDE : f.isCentre CDE)
    (hb : b.onCircle ABC) (he : e.onCircle CDE)
    (heb : |(f─e)| = |(f─b)|) (hne : ABC ≠ CDE) :
    False := by
  euclid_apply (equal_circles f b e ABC CDE)
  euclid_finish

end Elements.Book3
