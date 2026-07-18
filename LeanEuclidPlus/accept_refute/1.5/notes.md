# Answer key — accept/refute test set (Euclid I.5)

Each `vN/` is an alternative NL proof of **Elements I.5** (isosceles ⇒ base angles equal, and the
angles under the base equal) + its faithful Lean sentence map (`Main.lean`, all bodies `sorry` =
Phase A). The version numbers are **shuffled** to hide identity; this file is the ground truth.

The three buckets correspond to the sufficient condition:
- **accept** ⟺ every step's claim is provable (fills to zero-sorry),
- **refute** ⟺ ≥1 step's claim is *refutable* (universally false — one bad step is enough),
- **stuck** ⟺ some step is *mixed* (neither provable nor refutable) and none is refutable.

## Correct — should ACCEPT

- **v5** — *Pappus.* Compares △ABC with △ACB by SAS `[Prop.1.4]` (no construction). Fully valid,
  no gaps; every step is true and completable to a zero-sorry proof.
- **v2** — *valid, but SKIPS a step.* Correct proof that folds the I.13 linear-pair step into
  "since ∠ABC together with ∠CBD makes two right-angles …" **assumptions** instead of proving it as a
  sentence. The folded facts are TRUE but non-obvious, so the assumption sweep marks them
  `@assumption_gap` (real Phase-B obligations, provable via `[Prop.1.13]`). Accept-with-deferred-gaps —
  the gaps are legitimate, not a flaw.

## Incorrect — our method REFUTES it (contains a false, refutable step)

- **v3** — false step at **position 1**: claims ∠ABC and ∠ACB are right angles. Refutable (a base
  angle is always < 90°, via `[Prop.1.32]`). Caught immediately. `Main.lean` carries the machine
  proof `refute_step1 : ¬(∠ABC = ∟ ∧ ∠ACB = ∟)` + `contradiction : False`.
- **v1** — **valid prefix** (base angles + the two linear pairs are correct), then false step at
  **position 3**: claims ∠CBD is a right angle. Refutable (∠CBD is obtuse = 2∟ − base angle). Caught
  mid-proof. Carries `refute_step3 : ¬(∠CBD = ∟)` + `contradiction : False`.

## Incorrect — our method DOES NOT work (mixed step; needs a countermodel)

- **v4** — asserts the triangle is **equilateral** (`|BC| = |AB|`). This claim is **MIXED**: true in an
  equilateral isosceles triangle, false otherwise. So it is **neither provable** (can't accept — a
  non-equilateral isosceles triangle satisfies the hypotheses) **nor refutable** (can't disprove it —
  an equilateral one does too). Every *other* step in v4 is true, so there is no refutable step to
  fall back on. The syntactic accept/refute method is **stuck**: rejecting v4 requires an explicit
  **countermodel** `∃ config, H ∧ |BC| ≠ |AB|` (a concrete non-equilateral isosceles triangle /
  coordinates) — a semantic argument outside the sufficient condition.

## Summary

| version | verdict | why | method result |
|---------|---------|-----|----------------|
| v1 | incorrect | false step 3 (∠CBD = ∟) | **refute** ✓ |
| v2 | correct  | skips I.13 → 2 gaps (true, deferred) | **accept** ✓ |
| v3 | incorrect | false step 1 (∠ABC,∠ACB = ∟) | **refute** ✓ |
| v4 | incorrect | mixed step (equilateral) | **stuck** ✗ (needs countermodel) |
| v5 | correct  | Pappus, fully valid | **accept** ✓ |
