import AxiomSoundnessProofs.Interpretation.Helpers
import AxiomSoundnessProofs.Interpretation.Angles

/-!
# ℝ² interpretation — arcs

Mirrors `SystemE/Theory/Sorts/Arcs.lean`.  The SORT `Arc` (`ofPoints a b c`, arc from `a` to `c`
through `b`) gets a carrier and its constructor; the opaque magnitude `measure` is interpreted.

⚠ **SUBTLE / provisional.**  The arc measure is the central angle subtended by the arc `a→c` that
passes through `b`.  The minor/major (reflex) distinction — which of the two arcs `b` lies on — is
the delicate part.  No axiom currently PROVED uses `Arc.measure`, so this is a best-effort
interpretation to be pinned down when an arc axiom is tackled.
-/

namespace RInterp

/-- **`Arc`** (sort) ↦ its three points (arc from `a` to `c` through `b`). -/
structure Arc where
  a : Pt
  b : Pt
  c : Pt

/-- **`Arc.ofPoints`** (constructor) ↦ the three points. -/
def Arc.ofPoints (a b c : Pt) : Arc := ⟨a, b, c⟩

/-- **`Arc.measure` (`⌒ a:b:c`)** ↦ the central angle at the circumcentre subtended by `a` and `c`,
i.e. `∠ a o c` where `o` is the circumcentre of `a,b,c`.  (Minor/major convention TBD; see header.) -/
noncomputable def Arc.measure (ar : Arc) : ℝ :=
  Angle.degree (Angle.ofPoints ar.a (circumcenter ar.a ar.b ar.c) ar.c)

end RInterp
