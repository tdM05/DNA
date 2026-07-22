import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step5 (f c e : Point) (CDE : Circle)
  (hc : c.onCircle CDE) (he : e.onCircle CDE)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : f.isCentre CDE)   -- "point $F$ is the center of the circle $CDE$"
  : |(f─c)| = |(f─e)| := by
  euclid_apply (point_on_circle_onlyif f e c CDE)
  euclid_finish

end Elements.Book3
