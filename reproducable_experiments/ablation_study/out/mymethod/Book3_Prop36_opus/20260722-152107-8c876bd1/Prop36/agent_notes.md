# Prop36 (III.36) proving notes

Tangent-secant: |DA|*|DC| = |DB|^2. Two cases: DCA through center (steps1-11) / not (steps13-31).

## Cited props & signatures
- prop 3.18 `proposition_18 (c f)(ABC)(DE)`: c.onCircle ∧ c.onLine DE ∧ ¬DE.intersectsCircle ∧ f.isCentre ∧ f≠c → ∀ d, d.onLine DE → d≠c → ∠f:c:d=∟.  import Book3.Prop18.Main
  APPLY PATTERN: `euclid_apply (proposition_18 b f ABC DB (by euclid_finish) d hd_DB hdb)` — fully applied (antecedent + d + its two arrows), it CLOSES the goal directly (no trailing euclid_finish; that gives "no goals").
- prop 3.3 `proposition_3 (a b e f)(ABC)(AB CD)`: a,b onCircle ∧ distinctPointsOnLine a b AB ∧ e.isCentre ∧ e.onLine CD ∧ ¬e.onLine AB ∧ f.onLine AB ∧ f.onLine CD ∧ between a f b → (|a─f|=|f─b| → ∠a:f:e=∟) ∧ (∠a:f:e=∟ → |a─f|=|f─b|). import Book3.Prop03.Main
- prop 2.6 `Elements.Book2.proposition_6 (a b c d)(AB)`: distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧ between a c b ∧ |a─c|=|c─b| ∧ between a b d → |a─d|*|d─b| + |c─b|*|c─b| = |c─d|*|c─d|. import Book2.Prop06.Main
- prop 1.47 `Elements.Book1.proposition_47 (a b c)(AB BC AC)`: formTriangle a b c AB BC AC ∧ ∠b:a:c=∟ → |b─c|*|b─c| = |b─a|*|b─a| + |a─c|*|a─c|. import Book1.Prop47.Main. Right-angle vertex = prop's `a`.
- formTriangle a b c AB BC CA := distinctPointsOnLine a b AB ∧ b,c on BC ∧ c,a on CA ∧ AB≠BC ∧ BC≠CA ∧ CA≠AB.

## Workflow reminders
- scaffold puts `end Elements.Book3` already — when replacing the theorem block do NOT re-add `end`.
- linarith/nlinarith need `import Mathlib.Tactic.Linarith`.
- After proving a leaf, must run `--drive` to advance manifest frontier (bare check_step does NOT mark done). Hook blocks creating step(N+1).lean until stepN certified via --drive.
- Case-1 f = center on DA. Case-2 e=center (prop_1), f = foot of perp from e to AC (prop_12 a c e DA).

## Step map (Case 1: through center, F=center on DA)
- step1: excluded middle. DONE (Classical.em).
- step2: distinctPointsOnLine f b FB. DONE (euclid_finish; f≠b from center/circle).
- step3: ∠f:b:d=∟ via prop3.18 (tangent DB at b). DONE.
- step4: |a─f|+|c─d| = |f─c|+|c─d|. linarith from |a─f|=|f─c|. DONE.
- step5: |d─a|*|d─c| + |f─c|² = |f─d|² via prop2.6 `proposition_6 a c f d DA`. DONE.
- step6: |f─c|=|f─b|. radii. euclid_finish (f centre, c,b on circle).
- step7: |d─a|*|d─c| + |f─b|² = |f─d|². from step5,step6 substitution. euclid_finish/nlinarith.
- step8: |f─d|² = |f─b|² + |d─b|² via prop1.47 on rt triangle F B D, right angle at b (step3). `proposition_47 b f d FB DA DB`? line f-d = DA (f,d on DA). formTriangle b f d FB DA DB.
- step9: |d─a|*|d─c| + |f─b|² = |f─b|² + |d─b|². from step7,step8. linarith.
- step10: |d─a|*|d─c| = |d─b|*|d─b|. subtract. linarith from step9.
- step11: same as step10 (restate). from step10. linarith/exact.

## Step map (Case 2: E=center not on DA; F=foot of perp)
- step13: e.isCentre ABC. from prop_1 output. euclid_finish/assumption.
- step14: f.onLine DA ∧ distinctPointsOnLine e f EF ∧ (∠a:f:e=∟ ∨ ∠c:f:e=∟). from prop_12 output. 
- step15: distinctPointsOnLine e b EB ∧ e c EC ∧ e d ED. from line_from_points. euclid_finish.
- step16: ∠e:b:d=∟ via prop3.18 (tangent DB at b, e centre). like step3.
- step17: |a─f|=|f─c| via prop3.3 (EF thru center perp to AC bisects). assumption gives EF-thru-center-perp facts.
- step18: |a─f|=|f─c| (restate step17).
- step19: |a─f|=|f─c| (restate, CD added — claim is just eq). 
- step20: |d─a|*|d─c| + |f─c|² = |f─d|² via prop2.6 (same as step5).
- step21: + |e─f|² both sides. linarith from step20.
- step22: restate step21.
- step23: |e─c|² = |f─c|² + |e─f|² via prop1.47 rt triangle at f (∠e:f:c=∟). assump ∠e:f:c=∟.
- step24: |e─d|² = |d─f|² + |f─e|² via prop1.47 rt triangle at f (∠e:f:d=∟ / ∠d:f:e).
- step25: |d─a|*|d─c| + |e─c|² = |e─d|². from step22,23,24. nlinarith.
- step26: |e─c|=|e─b|. radii.
- step27: |d─a|*|d─c| + |e─b|² = |e─d|². from step25,26.
- step28: |e─b|²+|d─b|² = |e─d|² via prop1.47 rt triangle at b (∠e:b:d=∟, step16).
- step29: |d─a|*|d─c| + |e─b|² = |e─b|²+|d─b|². from step27,28.
- step30: |d─a|*|d─c| = |d─b|². subtract. linarith.
- step31: restate step30.
