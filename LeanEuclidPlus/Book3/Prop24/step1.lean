import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_24_step1
  (a b c d a' b' : Point) (CD : Line) (ImgSegment : Point → Point)
  (h_ImgSeg_b : ImgSegment b = b')
  (h_len : |(a─b)| = |(a'─b')|)
  (h_a'c : a' = c)
  (h_c_CD : c.onLine CD)
  (h_d_CD : d.onLine CD)
  (h_notbetween : ¬ between b' c d)
  (h_cd : c ≠ d)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ImgSegment a = c)   -- "point $A$ is placed on (point) $C$"
  (hassump2 : (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)   -- "the straight-line $AB$ on $CD$"
  (hassump3 : |(a─b)| = |(c─d)|)   -- "$AB$ being equal to $CD$"
  : ImgSegment b = d := by
  rw [h_ImgSeg_b]
  -- b' lies on CD (from the coincidence assumption)
  have hb'CD : b'.onLine CD := h_ImgSeg_b ▸ hassump2.2
  -- |c─b'| = |a─b| = |c─d|, so the two points b' and d are equidistant from c on CD
  have hlen : |(c─b')| = |(c─d)| := by
    have : |(a'─b')| = |(c─d)| := by rw [← h_len]; exact hassump3
    rw [h_a'c] at this; exact this
  -- discharge the function-typed maps before euclid_finish (SMT-translator trap)
  clear hassump1 hassump2 h_ImgSeg_b ImgSegment
  euclid_finish

end Elements.Book3
