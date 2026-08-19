import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- 3.24.7: "Thus, it will coincide." Double-negation elimination of step6's ¬¬(coincidence).
theorem helper_3_24_step7
  (a e b c d : Point) (CFD : Circle)
  (ImgSegment : Point → Point)
  (step6 : ¬(¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD)))
  : ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD :=
  Classical.not_not.mp step6

end Elements.Book3
