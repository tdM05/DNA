import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step7 (g d h : Point)
    (hbet : between g d h) (hstep6 : |(g─d)| > |(g─h)|) :
    False := by
  euclid_finish

end Elements.Book3
