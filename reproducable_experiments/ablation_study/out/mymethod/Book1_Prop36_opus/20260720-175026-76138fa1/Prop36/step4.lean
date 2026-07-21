import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step4 (b c e h : Point) (BE CH : Line)
    (hstep1 : distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH) :
    distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH := by
  euclid_finish

end Elements.Book1
