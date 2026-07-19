import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_3_step3 (a d e : Point) (DEF : Circle)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : a.isCentre DEF)   -- "point $A$ is the center of  circle $DEF$"
  (he : e.onCircle DEF) (hd : d.onCircle DEF)
  : |(a─e)| = |(a─d)| := by
  euclid_finish

end Elements.Book1
