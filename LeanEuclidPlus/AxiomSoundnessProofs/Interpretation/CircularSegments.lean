import AxiomSoundnessProofs.Interpretation.Relations

/-!
# ℝ² interpretation — circular segments

Mirrors `SystemE/Theory/Sorts/CircularSegments.lean` (the `area` magnitude) plus the
`CircularSegment.inside` / `.outside` relations from `SystemE/Theory/Relations.lean`.

The object sort `CircularSegment` is `ofPoints a b c`.  The segment REGION (part of the disk
through `a,b,c` on `b`'s side of chord `a─c`) is the scaffolding for `area`; kept `private` here
since it interprets no primitive on its own.
-/

namespace ESound

open MeasureTheory Classical

/-- The segment region: `disk ∩ half-plane`, or `∅` if `a,b,c` are collinear (junk value so
`area` is total, exactly as in the paper interpretation).  Scaffolding for `segArea` (interprets
no primitive on its own, but exposed so soundness proofs can reason about the region). -/
noncomputable def segRegion (a b c : Pt) : Set Pt :=
  if collinear a b c then ∅ else diskOf a b c ∩ halfOf a b c

/-- **`CircularSegment.area` (`⌓ a:b:c`)** ↦ the Lebesgue area of the segment region. -/
noncomputable def segArea (a b c : Pt) : ℝ := (volume (segRegion a b c)).toReal

/-- **`CircularSegment.inside`** `s t` ↦ `s`'s region ⊆ `t`'s region (proper). -/
def segInside (sa sb sc ta tb tc : Pt) : Prop :=
  segRegion sa sb sc ⊂ segRegion ta tb tc

/-- **`CircularSegment.outside`** `s t` ↦ the regions meet only in the shared chord (interiors
disjoint). -/
def segOutside (sa sb sc ta tb tc : Pt) : Prop :=
  interior (segRegion sa sb sc) ∩ interior (segRegion ta tb tc) = ∅

end ESound
