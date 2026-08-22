import AxiomSoundnessProofs.Interpretation.Helpers

/-!
# ℝ² interpretation — circular segments

Mirrors `SystemE/Theory/Sorts/CircularSegments.lean` (the SORT `CircularSegment` + its `area`
magnitude) and the `CircularSegment.inside` / `.outside` relations from `SystemE/Theory/Relations.lean`.

The sort `CircularSegment` (`ofPoints a b c`) is interpreted by a carrier and its constructor; the
segment REGION (part of the disk through `a,b,c` on `b`'s side of chord `a─c`) is the scaffolding
`area`/`inside`/`outside` are defined from.
-/

namespace RInterp

open MeasureTheory Classical

/-- **`CircularSegment`** (sort) ↦ its three points (`a`, `c` chord endpoints, `b` on the arc). -/
structure CircularSegment where
  a : Pt
  b : Pt
  c : Pt

/-- **`CircularSegment.ofPoints`** (constructor) ↦ the three points. -/
def CircularSegment.ofPoints (a b c : Pt) : CircularSegment := ⟨a, b, c⟩

noncomputable def CircularSegment.region (s : CircularSegment) : Set Pt :=
  if h : collinear s.a s.b s.c then ∅ else diskOf s.a s.b s.c h ∩ halfOf s.a s.b s.c

noncomputable def CircularSegment.area (s : CircularSegment) : ℝ :=
  (volume s.region).toReal

end RInterp
