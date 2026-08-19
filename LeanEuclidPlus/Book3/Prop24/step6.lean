import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- 3.24.6: "if AB is applied to CD, the segment AEB cannot NOT coincide with CFD." This is the
-- reductio-close: the block habsurd1 above (which used III.10) already established the double negation.
theorem helper_3_24_step6
  (a e b c d : Point) (CD : Line) (CFD : Circle)
  (ImgSegment : Point → Point)
  (habsurd1 : ¬(¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD)))
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)   -- "the straight-line $AB$ is applied to $CD$"
  : ¬(¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD)) :=
  habsurd1

end Elements.Book3
