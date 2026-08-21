import AxiomSoundnessProofs.Interpretation.Helpers
import AxiomSoundnessProofs.Interpretation.Angles

/-!
# ℝ² interpretation — arcs

Mirrors `SystemE/Theory/Sorts/Arcs.lean`.  Object sort `Arc` is `ofPoints a b c` (arc from `a`
to `c` through `b`); the opaque magnitude to interpret is `measure`.

⚠ **SUBTLE / provisional.**  The arc measure is the central angle subtended by the arc `a→c` that
passes through `b`.  The minor/major (reflex) distinction — which of the two arcs `b` lies on — is
the delicate part.  No axiom currently PROVED uses `Arc.measure`, so this is a best-effort
interpretation to be pinned down when an arc axiom is tackled.
-/

namespace ESound

/-- **`Arc.measure` (`⌒ a:b:c`)** ↦ the central angle at the circumcentre subtended by `a` and `c`,
i.e. `∠ a o c` where `o` is the circumcentre of `a,b,c`.  (Minor/major convention TBD; see header.) -/
noncomputable def arcMeasure (a b c : Pt) : ℝ :=
  let o := circumcenter a b c
  degree a o c

end ESound
