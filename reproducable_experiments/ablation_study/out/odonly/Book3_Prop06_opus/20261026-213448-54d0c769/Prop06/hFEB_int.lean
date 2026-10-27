import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_hFEB_int (CDE : Circle) (FEB : Line) (f : Point)
    (hfCDE : f.isCentre CDE) (hf : f.onLine FEB) :
    FEB.intersectsCircle CDE := by
  euclid_finish

end Elements.Book3
