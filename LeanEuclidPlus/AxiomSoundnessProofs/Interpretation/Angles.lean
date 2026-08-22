import AxiomSoundnessProofs.Interpretation.Helpers
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# ℝ² interpretation — angles

Mirrors `SystemE/Theory/Sorts/Angles.lean`.  The SORT `Angle` (`ofPoints a b c`) gets a carrier and
its constructor; the opaque magnitude `degree` and the constant `Right` are interpreted.

`degree` is the standard unoriented angle at the vertex `b` in `[0, π]`, `arccos` of the normalized
dot product of the rays `b→a`, `b→c` — no `EuclideanSpace` cast.
-/

namespace RInterp

/-- **`Angle`** (sort) ↦ its three points (vertex is the middle `b`). -/
structure Angle where
  a : Pt
  b : Pt
  c : Pt

/-- **`Angle.ofPoints`** (constructor) ↦ the three points. -/
def Angle.ofPoints (a b c : Pt) : Angle := ⟨a, b, c⟩

/-- **`Angle.degree` (`∠ a:b:c`)** ↦ the unoriented angle at the vertex `b`:
`arccos ( (b→a)·(b→c) / (|b→a|·|b→c|) ) ∈ [0, π]`. -/
noncomputable def Angle.degree (ang : Angle) : ℝ :=
  Real.arccos (dot (ang.a - ang.b) (ang.c - ang.b) /
    (Real.sqrt (dot (ang.a - ang.b) (ang.a - ang.b)) *
     Real.sqrt (dot (ang.c - ang.b) (ang.c - ang.b))))

/-- **`Angle.Right` (`∟`)** ↦ `π/2`. -/
noncomputable def Right : ℝ := Real.pi / 2

end RInterp
