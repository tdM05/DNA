import AxiomSoundnessProofs.Interpretation.Relations

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

/-- The 2-D REGION a circular segment denotes: the part of the disk through its three points on the
arc-point's side of the chord — `disk ∩ half-plane` — or `∅` if the three points are collinear
(junk value so `area` is total, exactly as in the paper interpretation).  This is the geometric
meaning of the sort; `area`/`inside`/`outside` are all defined from it. -/
noncomputable def CircularSegment.region (s : CircularSegment) : Set Pt :=
  if collinear s.a s.b s.c then ∅ else diskOf s.a s.b s.c ∩ halfOf s.a s.b s.c

/-- **`CircularSegment.area` (`⌓ a:b:c`)** ↦ the Lebesgue area of the segment region. -/
noncomputable def CircularSegment.area (s : CircularSegment) : ℝ :=
  (volume s.region).toReal

/-- **`CircularSegment.inside`** `s t` ↦ `s`'s region ⊆ `t`'s region (proper). -/
def CircularSegment.inside (s t : CircularSegment) : Prop := s.region ⊂ t.region

/-- **`CircularSegment.outside`** `s t` ↦ the regions meet only in the shared chord (interiors
disjoint). -/
def CircularSegment.outside (s t : CircularSegment) : Prop :=
  interior s.region ∩ interior t.region = ∅

end RInterp
