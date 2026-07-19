import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_3_step3 (a d e : Point) (DEF : Circle)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : a.isCentre DEF)   -- "point $A$ is the center of  circle $DEF$"
  (h_d : d.onCircle DEF) (h_e : e.onCircle DEF)
  : |(a─e)| = |(a─d)| := by
  euclid_apply (point_on_circle_onlyif a d e DEF)
  euclid_finish

end Elements.Book1
