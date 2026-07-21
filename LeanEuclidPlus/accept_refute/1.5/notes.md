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

## Incorrect — refuted by ROUTE B (mixed step; syntactic countermodel in System E)

For a **mixed** step the naive forced-false refute `H → ¬φ` FAILS (φ is true in some admissible
config). But the step is still refutable if the countermodel `∃ config, H ∧ ¬φ` is *constructible
inside System E* — **Route B**. By soundness, if System E deduced φ then φ would hold in every
model of H; a witnessed countermodel proves it does not. The cost is the witness construction,
which scales with the bad step: cheap when an equilateral base (Euclid I.1) suffices, expensive
when a non-equilateral triangle is required. `euclid_finish` cannot synthesise these witnesses, so
each `refute.lean` builds them by hand from the raw construction axioms (no `proposition_1`, hence
no `sorryAx`). All compiled clean via `lake env lean` + the leaneuclid venv; `#print axioms` shows
only geometric axioms + standard Lean axioms.

- **v4** — asserts the triangle is **equilateral** (`|BC| = |AB|`). MIXED (true for an equilateral
  isosceles, false otherwise). The countermodel needs a **non-equilateral** isosceles triangle —
  the hard case (previously "stuck"). `v4/refute.lean` builds one: `m` between `a,b`; circle
  `α=(a,|ab|)`, circle `γ=(b,|bm|)`; apex `c = α ∩ γ` gives `|ac|=|ab|` and `|bc|=|bm|<|ab|`.
  `routeB_refute_step1 : ∃ a b c d e …, H ∧ ¬(|(b─c)| = |(a─b)|)`. **Axiom-clean.**

## Summary

| version | verdict | why | method result |
|---------|---------|-----|----------------|
| v1 | incorrect | false step 3 (∠CBD = ∟) | **refute** ✓ |
| v2 | correct  | skips I.13 → 2 gaps (true, deferred) | **accept** ✓ |
| v3 | incorrect | false step 1 (∠ABC,∠ACB = ∟) | **refute** ✓ |
| v4 | incorrect | mixed step (equilateral) | **Route B** ✓ (non-equilateral countermodel, `refute.lean`) |
| v5 | correct  | Pappus, fully valid | **accept** ✓ |
