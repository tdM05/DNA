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

namespace RInterp

open MeasureTheory Classical

/-- Dot product of two ℝ² vectors: `u·v = u.1·v.1 + u.2·v.2`. -/
def dot (u v : Pt) : ℝ := u.1 * v.1 + u.2 * v.2

/-- 2-D cross product (a scalar): `u × v = u.1·v.2 − u.2·v.1`.  Its sign is orientation, its
absolute value twice the triangle area, and it is `0` iff `u, v` are parallel. -/
def cross (u v : Pt) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Evaluate a line where we move all variables on one side of the equation: `ℓ_L(p) = a·p.1 + b·p.2 − c`.
Can ask if this is equal to 0 to check if p is on the line L. -/
def ℓ (L : Line) (p : Pt) : ℝ := dot (L.a, L.b) p - L.c

/-- `a, b, c` are collinear ↔ the cross product `(b−a)×(c−a) = 0`. -/
def collinear (a b c : Pt) : Prop := cross (b - a) (c - a) = 0

/-- **The defining property of a circumcentre**: `o` is equidistant from `a, b, c`,
`‖o−a‖ = ‖o−b‖ = ‖o−c‖` (stated with squared distances `dot (o−·) (o−·)` to stay polynomial;
`‖·‖` is the monotone square root, so equal squares ⟺ equal distances). -/
def Equidistant (a b c o : Pt) : Prop :=
  dot (o - a) (o - a) = dot (o - b) (o - b) ∧ dot (o - b) (o - b) = dot (o - c) (o - c)

/-- **The circumcentre exists and is unique** for non-collinear `a, b, c`: there is exactly one point
equidistant from all three.  (Existence witness = Cramer's rule on the two perpendicular-bisector
equations `‖o−a‖²=‖o−b‖²`, `‖o−b‖²=‖o−c‖²`, whose `‖o‖²` terms cancel to a linear 2×2 system;
uniqueness because that system is nonsingular when non-collinear.)  This is the REAL content — the
messy coordinate formula appears only here, as the hidden witness, and is never read again. -/
theorem exists_unique_circumcenter (a b c : Pt) (h : ¬ collinear a b c) :
    ∃! o : Pt, Equidistant a b c o := by
  unfold collinear cross at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  have hD : 2 * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)) ≠ 0 := by
    intro hz; apply h; linarith
  -- the explicit circumcentre (Cramer), the sole appearance of the formula
  refine ⟨( ((a.1^2 + a.2^2) * (b.2 - c.2) + (b.1^2 + b.2^2) * (c.2 - a.2)
              + (c.1^2 + c.2^2) * (a.2 - b.2))
            / (2 * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)))
          , ((a.1^2 + a.2^2) * (c.1 - b.1) + (b.1^2 + b.2^2) * (a.1 - c.1)
              + (c.1^2 + c.2^2) * (b.1 - a.1))
            / (2 * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1))) ),
          ?_, ?_⟩
  · -- the formula is equidistant
    refine ⟨?_, ?_⟩ <;>
      simp only [Equidistant, dot, Prod.fst_sub, Prod.snd_sub] <;> field_simp <;> ring
  · -- uniqueness: any equidistant point equals the Cramer point.
    -- h1, h2 are secretly LINEAR in o (the o² terms cancel); the goal is Cramer's solution, so it
    -- is a fixed linear combination of h1, h2 — `linear_combination`, not `nlinarith`.
    rintro o ⟨h1, h2⟩
    simp only [Equidistant, dot, Prod.fst_sub, Prod.snd_sub] at h1 h2
    apply Prod.ext
    · show o.1 = _
      field_simp
      linear_combination (c.2 - b.2) * h1 + (a.2 - b.2) * h2
    · show o.2 = _
      field_simp
      linear_combination (b.1 - c.1) * h1 + (b.1 - a.1) * h2

/-- `(p − a) × (c − a)`, whose sign says which side of chord `a─c` the point `p` is on. -/
def chordForm (a c : Pt) (p : Pt) : ℝ := cross (p - a) (c - a)

/-- The closed disk through non-collinear `a,b,c` (centre `o` = the circumcentre, radius = its
distance to `a`): `‖p − o‖² ≤ ‖a − o‖²`. -/
def diskOf (a b c : Pt) (h : ¬ collinear a b c) : Set Pt :=
  let o := (exists_unique_circumcenter a b c h).choose
  { p | dot (p - o) (p - o) ≤ dot (a - o) (a - o) }

/-- The closed half-plane bounded by chord `a─c` on `b`'s side. Inuitively p and b are on same side.-/
def halfOf (a b c : Pt) : Set Pt :=
  { p | chordForm a c p * chordForm a c b ≥ 0 }

end RInterp
