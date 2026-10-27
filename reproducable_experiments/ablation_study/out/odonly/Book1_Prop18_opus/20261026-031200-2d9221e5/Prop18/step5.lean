import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step5 (a b c d : Point) (BC AC : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hadc : between a d c)
    (hstep3 : ∠ a:d:b > ∠ d:c:b)
    (hstep4 : ∠ a:d:b = ∠ a:b:d) :
    ∠ a:b:d > ∠ b:c:a := by
  euclid_finish

end Elements.Book1
