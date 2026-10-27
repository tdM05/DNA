# Prop36 (III.36) Phase-B plan

Secant DCA from external D cuts circle ABC (a,c on circle; between d c a), DB tangent at b.
Goal: |(d─a)|·|(d─c)| = |(d─b)|·|(d─b)|.  Two cases (through center / not).

## Key cited lemmas (signatures verified)
- III.18 `proposition_18 (c f:Point)(ABC:Circle)(DE:Line)`: c.onCircle ∧ c.onLine DE ∧ ¬DE.intersectsCircle ∧ f.isCentre ∧ f≠c → ∀ d, d.onLine DE → d≠c → ∠ f:c:d = ∟.  Apply FULLY: `euclid_apply (proposition_18 b f ABC DB (by euclid_finish) d hdDB hdb)` (close-directly path; returns ∀ so can't use `as`).
- II.6 `Elements.Book2.proposition_6 (a b c d:Point)(AB:Line)`: distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧ between a c b ∧ |a-c|=|c-b| ∧ between a b d → |(a─d)|·|(d─b)| + |(c─b)|² = |(c─d)|².  import Book2.Prop06.Main
- I.47 `proposition_47 (a b c:Point)(AB BC AC:Line)`: formTriangle a b c AB BC AC ∧ ∠ b:a:c = ∟ → |(b─c)|² = |(b─a)|² + |(a─c)|². (right angle at a). import Book1.Prop47.Main
- III.3 `proposition_3 (a b e f:Point)(ABC:Circle)(AB CD:Line)`: a,b onCircle ∧ distinctPointsOnLine a b AB ∧ e.isCentre ∧ e.onLine CD ∧ ¬e.onLine AB ∧ f.onLine AB ∧ f.onLine CD ∧ between a f b → (|a-f|=|f-b| → ∠ a:f:e=∟) ∧ (∠ a:f:e=∟ → |a-f|=|f-b|). import Book3.Prop03.Main

## Per-step
Case1:
- step2 ✓ distinctPointsOnLine f b FB (euclid_finish)
- step3 ∠ f:b:d=∟  [III.18]  (b=contact, f=centre, DE=DB)  — in flight
- step4 |a-f|+|c-d| = |f-c|+|c-d|  :  `rw [hassump1]` (hassump1 : |a-f|=|f-c|)
- step5 |d-a|·|d-c| + |f-c|² = |f-d|²  [II.6] map a:=a,b:=c,c:=f,d:=d,AB:=DA; then euclid_finish to fix |a-d|=|d-a|
- step6 |f-c|=|f-b|  radii (euclid_finish; c,b on circle, f centre)
- step7 |d-a|·|d-c| + |f-b|² = |f-d|²  : from step5,step6 (euclid_finish — squares equality)
- step8 |f-d|² = |f-b|² + |d-b|²  [I.47] triangle f b d, right∠ at b (step3), lines FB,DB,DA(=fd)
- step9 |d-a|·|d-c| + |f-b|² = |f-b|² + |d-b|²  : step7,step8 linarith/euclid_finish
- step10 |d-a|·|d-c| = |d-b|²  : step9 linarith
- step11 = step10 (exact/euclid_finish from step10)
Case2 (e=centre via prop_1, f=foot via prop_12, EF perp):
- step13 e.isCentre ABC (euclid_finish/assumption from prop_1 output)
- step14 f.onLine DA ∧ distinctPointsOnLine e f EF ∧ (∠ a:f:e=∟ ∨ ∠ c:f:e=∟)  [I.12] from prop_12 output
- step15 distinctPointsOnLine e b EB ∧ e c EC ∧ e d ED  (euclid_finish)
- step16 ∠ e:b:d=∟  [III.18]
- step17 |a-f|=|f-c|  [III.3] 2nd conjunct; need ∠ a:f:e=∟ (derive from the ∨ + straight angle)
- step18 |a-f|=|f-c| = step17
- step19 |a-f|=|f-c| (assumption restate)
- step20 |d-a|·|d-c| + |f-c|² = |f-d|²  [II.6]
- step21 +|e-f|² both sides  (linarith from step20)
- step22 = step21 (linarith)
- step23 |e-c|² = |f-c|² + |e-f|²  [I.47] right∠ e:f:c (step23_assumption1)
- step24 |e-d|² = |d-f|² + |f-e|²  [I.47] right∠ at f
- step25 |d-a|·|d-c| + |e-c|² = |e-d|²  : step22,23,24
- step26 |e-c|=|e-b| radii
- step27 |d-a|·|d-c| + |e-b|² = |e-d|²  : step25,26
- step28 |e-b|² + |d-b|² = |e-d|²  [I.47] right∠ e:b:d (step16)
- step29 |d-a|·|d-c| + |e-b|² = |e-b|² + |d-b|²  : step27,28
- step30 |d-a|·|d-c| = |d-b|²  : step29 linarith
- step31 = step30

## Workflow notes
- cwd resets to repo root each turn → `cd LeanEuclidPlus` first.
- Builds slow (Main re-runs @assumption euclid_finish every build). Use <<<RUN>>> channel if >10min.
- In-order discipline: edit stepN only when it's the frontier (step N-1 done & not stale). Re-drive after edits.
