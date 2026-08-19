import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Classical in
theorem helper_3_24_step3
  (a e b c f d : Point) (CD : Line) (CFD : Circle)
  (ImgSegment : Point → Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)   -- "the straight-line $AB$ coincides with $CD$"
  (hassump2 : ¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD))   -- "the segment $AEB$ does not coincide with $CFD$"
  -- mseg / tseg are `let`s in Main; stated here in their unfolded `CircularSegment.ofPoints` form
  : (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).inside (CircularSegment.ofPoints c f d)
    ∨ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).outside (CircularSegment.ofPoints c f d)
    ∨ (¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).inside (CircularSegment.ofPoints c f d)
       ∧ ¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).outside (CircularSegment.ofPoints c f d)) := by
  -- pure classical trichotomy: p ∨ q ∨ (¬p ∧ ¬q)
  set mseg := CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)
  set tseg := CircularSegment.ofPoints c f d
  by_cases hin : mseg.inside tseg
  · exact Or.inl hin
  · by_cases hout : mseg.outside tseg
    · exact Or.inr (Or.inl hout)
    · exact Or.inr (Or.inr ⟨hin, hout⟩)

end Elements.Book3
