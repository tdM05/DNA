import AxiomSoundnessProofs.Interpretation.Primitives
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic

/-!
# ℝ² geometry helpers

Pure ℝ² math used *inside* the interpretations.  **These interpret NO System-E primitive** — they
are shared scaffolding (this is the one file that does not mirror `SystemE/Theory/`).  Broadly
reused helpers live here; single-use scaffolding stays `private` beside the interpretation it
serves (e.g. `segArea` in `CircularSegments.lean`).
-/

namespace ESound

open MeasureTheory

/-- Dot product of two ℝ² vectors: `u·v = u.1·v.1 + u.2·v.2`. -/
def dot (u v : Pt) : ℝ := u.1 * v.1 + u.2 * v.2

/-- 2-D cross product (a scalar): `u × v = u.1·v.2 − u.2·v.1`.  Its sign is orientation, its
absolute value twice the triangle area, and it is `0` iff `u, v` are parallel. -/
def cross (u v : Pt) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Evaluate a line where we move all variables on one side of the equation: `ℓ_L(p) = a·p.1 + b·p.2 − c`.
Can ask if this is equal to 0 to check if p is on the line L. -/
def ℓ (L : Line) (p : Pt) : ℝ := dot (L.a, L.b) p - L.c

/-- The determinant `D = 2·(b−a)×(c−a)` in the circumcentre formula (nonzero iff non-collinear). -/
def circumDet (a b c : Pt) : ℝ := 2 * cross (b - a) (c - a)

/-- The circumcentre of `a,b,c` (standard formula; meaningful when non-collinear). -/
noncomputable def circumcenter (a b c : Pt) : Pt :=
  ( ((a.1^2 + a.2^2) * (b.2 - c.2) + (b.1^2 + b.2^2) * (c.2 - a.2)
      + (c.1^2 + c.2^2) * (a.2 - b.2)) / circumDet a b c
  , ((a.1^2 + a.2^2) * (c.1 - b.1) + (b.1^2 + b.2^2) * (a.1 - c.1)
      + (c.1^2 + c.2^2) * (b.1 - a.1)) / circumDet a b c )

/-- Affine form of the chord line through `a` and `c` (used to pick a segment's side):
`(p − a) × (c − a)`, whose sign says which side of chord `a─c` the point `p` is on. -/
def chordForm (a c : Pt) (p : Pt) : ℝ := cross (p - a) (c - a)

/-- The closed disk through `a,b,c` (centre = circumcentre, radius = its distance to `a`). -/
def diskOf (a b c : Pt) : Set Pt :=
  let o := circumcenter a b c
  { p | (p.1 - o.1)^2 + (p.2 - o.2)^2 ≤ (a.1 - o.1)^2 + (a.2 - o.2)^2 }

/-- The closed half-plane bounded by chord `a─c` on `b`'s side. -/
def halfOf (a b c : Pt) : Set Pt :=
  { p | chordForm a c p * chordForm a c b ≥ 0 }

end ESound
