import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_hFEB_int (CDE : Circle) (FEB : Line) (f : Point)
    (hfCDE : f.isCentre CDE) (hf_on : f.onLine FEB) :
    FEB.intersectsCircle CDE := by
  euclid_apply (center_inside_circle f CDE)
  euclid_apply (intersection_circle_line_2 f CDE FEB)
  euclid_finish

end Elements.Book3
