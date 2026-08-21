import AxiomSoundnessProofs.Interpretation.Segments
import AxiomSoundnessProofs.Interpretation.Helpers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# ℝ² interpretation — angles

Mirrors `SystemE/Theory/Sorts/Angles.lean`.  The object sort `Angle` is `ofPoints a b c`;
what needs interpreting is the opaque magnitude `degree` and the constant `Right`.

`degree` is given explicitly over `ℝ×ℝ` as `arccos` of the normalized dot product of the two rays
`b→a` and `b→c` — the standard unoriented angle in `[0, π]` — avoiding any `EuclideanSpace` cast.
-/

namespace ESound

/-- **`Angle.degree` (`∠ a:b:c`)** ↦ the unoriented angle at `b`, i.e.
`arccos ( (b→a)·(b→c) / (|b→a|·|b→c|) ) ∈ [0, π]`. -/
noncomputable def degree (a b c : Pt) : ℝ :=
  Real.arccos (dot (a - b) (c - b) / (length b a * length b c))

/-- **`Angle.Right` (`∟`)** ↦ `π/2`. -/
noncomputable def Right : ℝ := Real.pi / 2

end ESound
