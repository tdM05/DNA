import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step7 (ABC CDE : Circle) (b e f : Point)
  (hne : ABC ≠ CDE)
  (hfABC : f.isCentre ABC) (hfCDE : f.isCentre CDE)
  (hb : b.onCircle ABC) (he : e.onCircle CDE)
  (hstep6 : |(f─e)| = |(f─b)|)
  : False := by
  euclid_finish

end Elements.Book3
