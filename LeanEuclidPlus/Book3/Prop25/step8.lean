import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step8 (a b c d e : Point) (AC DB EC : Line)
    (hAa : a.onLine AC) (hAc : c.onLine AC) (hbAC : ¬b.onLine AC)
    (hadc : between a d c) (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (heDB : e.onLine DB)
    (heEC : e.onLine EC) (hcEC : c.onLine EC) : distinctPointsOnLine e c EC := by
  euclid_finish

end Elements.Book3
