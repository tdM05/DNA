import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_24_step1_assumption2
  (a b a' b' : Point) (CD : Line) (ImgSegment : Point → Point)
  (h_ImgSeg_a : ImgSegment a = a')
  (h_ImgSeg_b : ImgSegment b = b')
  (h_a'_CD : a'.onLine CD)
  (h_b'_CD : b'.onLine CD)
  : (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD := by
  rw [h_ImgSeg_a, h_ImgSeg_b]
  exact ⟨h_a'_CD, h_b'_CD⟩

end Elements.Book3
