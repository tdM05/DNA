# Prop36 — agent notes

## Proof structure (Phase B, all certified)
- step1: distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH — from the two `line_from_points`
  constructions; distinctness derived in-body via euclid_finish (needs AH≠BG from the parallelogram atoms).
- step2_assumption2 (`@assumption_gap`): |FG|=|EH| via `proposition_34` on parallelogram EFGH.
- step2: |BC|=|EH| — genuinely applies `proposition_34` (FG=EH) then transitivity with BC=FG. (Satisfies
  the [Prop.1.34] citation of sentence 1.36.2 in step2's own cone.)
- step3: ¬BG.intersectsLine AH — parallel symmetry (euclid_finish).
- step4: reorder step1's distinctness facts (euclid_finish).
- step5: |EB|=|HC| ∧ ¬BE.intersects CH via `proposition_33` [Prop.1.33]. Sub-node **step5_ss**
  (`e.sameSide b CH`) — the crux figure fact; euclid_finish derives it from the full first-parallelogram
  context + `between a e h`. step5_ss is REUSED as a `have` in step6.
- step6: formParallelogram EBCH — definitional assembly (euclid_finish) reusing step5_ss + step5.
- step7: area(EBCH)=area(ABCD) via `proposition_35'` [Prop.1.35] (common base BC).
- step8: area(EFGH)=area(EBCH) via `proposition_35'` (common base EH; reoriented parallelograms handled
  by the SMT). Imports Book1Variants.Prop35 (proposition_35', which transitively uses the faithful
  proposition_35 + proposition_34').
- step9: transitivity of step7, step8 (linarith).

## ⚠ TWO @suppress_deps_check — NEEDS HUMAN REVIEW AT GATE C
Fitzpatrick's edition brackets both sentences 1.36.6 and 1.36.8 as `[Prop.~1.34]`, but the actual
System-E dependency differs (cross-checked against Heath's edition):
- **1.36.6** "EBCH is a parallelogram [Prop.1.34]": genuine dep is **Prop 1.33** (the equal-and-parallel
  joins EB,HC from sentence 1.36.5) + the parallelogram definition. Prop 1.34 concerns properties OF a
  parallelogram, not that a figure IS one. Heath cites [I.33]. step6 assembles formParallelogram
  definitionally (no proposition_34 in its cone — gate-C olean check would also not find one).
- **1.36.8** "EFGH equal to EBCH [Prop.1.34]": genuine dep is **Prop 1.35** ("for the same reasons" as
  1.36.7 = [Prop.1.35]; common base EH). Discharged via proposition_35', which transitively applies
  proposition_34' — so the gate-C olean check DOES credit [1.34]; only the number-only source check
  (which can't follow imports) needed waiving. Heath cites [I.35].

I did NOT apply proposition_34 gratuitously in either step (that would be gaming — its output is not
load-bearing for either claim). The source text is kept byte-for-byte verbatim; only the criterion-3
number check is waived, with the mandatory reason recorded inline. Please confirm the suppressions at
gate C.
