import AxiomSoundnessProofs.Interpretation.Helpers
import AxiomSoundnessProofs.Interpretation.Angles
import AxiomSoundnessProofs.Interpretation.Segments

/-!
# ℝ² interpretation — arcs

Mirrors `SystemE/Theory/Sorts/Arcs.lean`.  The SORT `Arc` is Euclid's "circumference" — the 1-D
piece of a circle's boundary from `a` to `c` through `b`.  So its magnitude `measure` is that
piece's **arc LENGTH** (a 1-D length, like `Segment.length`), = `ρ · θ` (radius × central angle).

⚠ **One real subtlety** (not length-vs-angle — that's settled, it's length): the central angle `∠ a o c`
below is the non-reflex angle in `[0, π]`, so this gives the MINOR-arc length.  If `b` lies on the
MAJOR arc, the true length through `b` is `ρ·(2π − θ)`.  No axiom currently uses `Arc.measure`, so
the reflex/which-arc branch is deferred until an arc axiom (Book III.26+) pins it down.
-/

namespace RInterp

open Classical

/-- **`Arc`** (sort) ↦ its three points (arc from `a` to `c` through `b`). -/
structure Arc where
  a : Pt
  b : Pt
  c : Pt

/-- **`Arc.ofPoints`** (constructor) ↦ the three points. -/
def Arc.ofPoints (a b c : Pt) : Arc := ⟨a, b, c⟩

/-- **`Arc.measure` (`⌒ a:b:c`)** ↦ the arc LENGTH `ρ · θ`, where `o` is the circumcentre of
`a,b,c` (from `exists_unique_circumcenter`), `ρ = ‖a − o‖` the radius, and `θ = ∠ a o c` the central
angle.  Junk `0` if the three points are collinear (a degenerate arc).  (Minor-arc; see header.) -/
noncomputable def Arc.measure (ar : Arc) : ℝ :=
  if h : collinear ar.a ar.b ar.c then 0
  else
    let o := (exists_unique_circumcenter ar.a ar.b ar.c h).choose
    let ρ := Segment.length (Segment.endpoints o ar.a)          -- radius = ‖o − a‖
    let θ := Angle.degree (Angle.ofPoints ar.a o ar.c)          -- central angle
    ρ * θ

end RInterp
