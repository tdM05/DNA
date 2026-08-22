import AxiomSoundnessProofs.Interpretation.Helpers
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# ℝ² interpretation — segments

Mirrors `SystemE/Theory/Sorts/Segments.lean`.  The SORT `Segment` (`endpoints a b`) gets a carrier
and its constructor; the opaque magnitude `length` becomes a function on that carrier.
-/

namespace RInterp

/-- **`Segment`** (sort) ↦ its two endpoints. -/
structure Segment where
  a : Pt
  b : Pt

/-- **`Segment.endpoints`** (constructor) ↦ the two endpoints. -/
def Segment.endpoints (a b : Pt) : Segment := ⟨a, b⟩

/-- **`Segment.length` (`|a─b|`)** ↦ Euclidean distance `√‖b − a‖²`. -/
noncomputable def Segment.length (s : Segment) : ℝ :=
  Real.sqrt (dot (s.b - s.a) (s.b - s.a))

end RInterp
