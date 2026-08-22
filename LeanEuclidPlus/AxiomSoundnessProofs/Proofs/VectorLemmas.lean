import AxiomSoundnessProofs.Interpretation

/-!
# Vector proof-lemmas (shared across soundness proofs)

`@[simp]` rewrites that unfold `dot`/`cross` on point-differences into the component form
`ring`/`linarith` need, pushing the `Prod` projections through the subtraction in one step (they
replace the `unfold dot; simp [Prod.fst_sub, Prod.snd_sub]` ritual).

These are PROOF support, not interpretation — they define no System-E symbol — so they live in
`Proofs/`, not in `Interpretation/`.
-/

namespace RInterp

/-- `dot (p−q) (r−s)` in component form (projections pushed through the subtraction). -/
@[simp] theorem dot_sub (p q r s : Pt) :
    dot (p - q) (r - s) = (p.1 - q.1) * (r.1 - s.1) + (p.2 - q.2) * (r.2 - s.2) := by
  unfold dot; simp [Prod.fst_sub, Prod.snd_sub]

/-- `cross (p−q) (r−s)` in component form (projections pushed through).  See `dot_sub`. -/
@[simp] theorem cross_sub (p q r s : Pt) :
    cross (p - q) (r - s) = (p.1 - q.1) * (r.2 - s.2) - (p.2 - q.2) * (r.1 - s.1) := by
  unfold cross; simp [Prod.fst_sub, Prod.snd_sub]

end RInterp
