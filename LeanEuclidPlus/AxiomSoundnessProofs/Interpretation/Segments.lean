import AxiomSoundnessProofs.Interpretation.Primitives
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# ℝ² interpretation — segments

Mirrors `SystemE/Theory/Sorts/Segments.lean`.  Object sort `Segment` is `endpoints a b`;
the opaque magnitude to interpret is `length`.
-/

namespace ESound

/-- **`Segment.length` (`|a─b|`)** ↦ Euclidean distance `√((bₓ−aₓ)² + (b_y−a_y)²)`. -/
noncomputable def length (a b : Pt) : ℝ :=
  Real.sqrt ((b.1 - a.1)^2 + (b.2 - a.2)^2)

end ESound
