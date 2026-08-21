import AxiomSoundnessProofs.Interpretation.Helpers

/-!
# ℝ² interpretation — triangles

Mirrors `SystemE/Theory/Sorts/Triangles.lean`.  Object sort `Triangle` is `ofPoints a b c`;
the opaque magnitude to interpret is `area`.
-/

namespace ESound

/-- **`Triangle.area` (`△ a:b:c`)** ↦ the shoelace area `|(b−a)×(c−a)| / 2`. -/
noncomputable def triArea (a b c : Pt) : ℝ :=
  |cross (b - a) (c - a)| / 2

end ESound
