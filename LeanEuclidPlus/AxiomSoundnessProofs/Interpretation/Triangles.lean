import AxiomSoundnessProofs.Interpretation.Helpers

/-!
# ℝ² interpretation — triangles

Mirrors `SystemE/Theory/Sorts/Triangles.lean`.  The SORT `Triangle` (`ofPoints a b c`) gets a
carrier and its constructor; the opaque magnitude `area` becomes a function on that carrier.
-/

namespace RInterp

/-- **`Triangle`** (sort) ↦ its three vertices. -/
structure Triangle where
  a : Pt
  b : Pt
  c : Pt

/-- **`Triangle.ofPoints`** (constructor) ↦ the three vertices. -/
def Triangle.ofPoints (a b c : Pt) : Triangle := ⟨a, b, c⟩

/-- **`Triangle.area` (`△ a:b:c`)** ↦ the shoelace area `|(b−a)×(c−a)| / 2`. -/
noncomputable def Triangle.area (t : Triangle) : ℝ :=
  |cross (t.b - t.a) (t.c - t.a)| / 2

end RInterp
