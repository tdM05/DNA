import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_24_step1_assumption1
  (a c a' : Point) (ImgSegment : Point → Point)
  (h_ImgSeg_a : ImgSegment a = a')
  (h_a'_c : a' = c)
  : ImgSegment a = c := by
  rw [h_ImgSeg_a, h_a'_c]

end Elements.Book3
