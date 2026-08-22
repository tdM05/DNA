# Soundness of System E via a single ℝ² interpretation `I`

## High level

System E's primitives are `opaque` / `axiom Type` — Lean knows nothing about them, so
axioms are applied by symbol-pushing and carry no meaning. To prove an axiom is **sound**
we fix the standard model `M = ℝ²` (Descartes/Tarski) and check the axiom is true there.

The mechanism is one interpretation `I` that turns any System-E statement into an ℝ²
statement, automatically:

- **Sorts → carriers.** `Point ↦ ℝ²`, `Line ↦` affine form, `Circle ↦ (center, radius)`.
- **Symbols → their ℝ² meaning.** `onCircle ↦ ‖p−o‖²=ρ²`, `degree ↦ ∠`, `area ↦ …`, etc.
- **An axiom → an ℝ² proposition**, obtained by replacing every symbol by its meaning and
  keeping the logical structure (`∀ ∧ → =`) as is.

Soundness of the whole system then follows the standard model-theoretic argument
(`M ⊨ Δ` + soundness of the proof system ⟹ Δ proves nothing `M` refutes). We only owe the
**delta**: the new axioms we added (the base ~100 are already sound, Avigad–Dean–Mumma 2009).

**The verdict principle.** A good primitive axiom has a *short* ℝ² proof. If the translated
goal is hard to prove, the axiom is bad — either bloated (split it) or unsound (a stuck proof
is exactly how we catch a false axiom).

## Where the difficulty is (and is NOT) — read this if confused

Three stages; only the last has any real work:

| stage | hard? |
|---|---|
| 1. write the interpretation `I` (~21 entries: `Point ↦ ℝ²`, `onCircle ↦ ‖p−o‖²=ρ²`, …) | trivial — just definitions |
| 2. apply `I` to an axiom → its ℝ² statement (the `Expr` walker) | mechanical, write once |
| 3. **prove the resulting ℝ² statement** | the ONLY real work — short if the axiom is good |

- The **interpretation is trivial.** No hard part.
- **Translation is trivial too.** `∀ (x : Point), P x` ↦ `∀ (x : ℝ²), I(P x)`. `∧ ↦ ∧`,
  `→ ↦ →`, leaves ↦ table. Exactly what it looks like; nothing hidden.
- The **only** thing left is *proving* `I(axiom)` holds in ℝ² — and that difficulty is the
  feature (it is the soundness check, per the verdict principle above).

### Binder footnote (implementation only, NOT a conceptual issue)
Lean stores a bound `∀`-variable as a nameless de Bruijn slot (`bvar 0`), not the name `x`.
So the code that does `∀ ↦ ∀` is 3 standard lines — open the binder, recurse, rebuild:
`withLocalDecl … (I ty) fun x => mkForallFVars #[x] (← I (body.instantiate1 x))`. This is
boilerplate copied once; it is not per-axiom and not a difficulty in the idea.

## How `I` is implemented

`I` is a **metaprogram** (a tactic/elaborator) that walks the axiom's native Lean `Expr`
— the same technique as `SystemE/Meta/Smt/Translator.lean`, but retargeted from SMT strings
to Mathlib ℝ² `Prop`s (so `inside`/`outside`/area-as-measure, which have no SMT counterpart,
are fine).

On an axiom's `Expr` it:
1. **auto-unfolds transparent defs** (`coincides`, `formCircularSegment`,
   `distinctPointsOnLine`, …) via `whnf`/`simp only` — Lean does this, no table needed;
2. **substitutes each opaque leaf** (`onCircle`, `sameSide`, `degree`, `area`, `Point`, …)
   using the hand-written interpretation table;
3. **walks the logical structure** (`∀`, `∧`, `→`, `=`, `¬`) structurally;
4. **emits the ℝ² goal**, which is then discharged by ordinary Mathlib tactics.

### What is manual (small, once, checkable)

- **The interpretation table (~21 entries).** One line per primitive sort / constant /
  function / relation. This *is* the interpretation — irreducible in any design; few enough
  to eyeball-verify against the standard cartesian meanings. **Single source of truth: each
  symbol mapped exactly once.**
- **The traversal tactic itself** — written once, trusted (analogue of `Translator.lean`).
- **The proofs** — after translation, each ℝ² goal is proven with tactics (short for good
  axioms; `∃`-axioms like `segment_superposition` need an explicit witness first).

### What is NOT manual / NOT redundant

- **Axioms are never rewritten.** The real axiom goes in verbatim; `I` translates it. No
  per-axiom hand mapping, ever.
- **No parallel copies of System-E structure.** We do not recreate `Segment`, `Angle`,
  `CircularSegment`, `coincides`, … — the axioms keep using the real types; only the opaque
  *leaves* hit the table.
- **Derived defs are free.** Transparent defs unfold to primitives that are already mapped,
  so `coincides` etc. are never given their own table entry.

### The interpretation table (the ~21 symbols to map)

Sorts: `Point ↦ ℝ²`, `Line`, `Circle`.
Constant: `Right ↦ π/2`.
Functions: `length ↦ dist`, `degree ↦ ∠`, `Triangle.area ↦` shoelace,
`Arc.measure ↦` central angle, `CircularSegment.area ↦ vol(disk ∩ half-plane)`.
Relations: `onLine`, `sameSide`, `collinear`, `between`, `onCircle`, `insideCircle`,
`isCentre`, `Line.intersectsLine`, `Line.intersectsCircle`, `Circle.intersectsCircle`,
`CircularSegment.inside`, `CircularSegment.outside`.

## Scope (now)

- Target model: **ℝ²** only (the standard model; metric-1 soundness).
- Prove only the **new** axioms we added (`coincide_equal_area`, `segment_superposition`,
  `segment_arc_crossing`, `segment_equal_angle_no_nest`); cite ADM 2009 for the base.
- **Not** in scope now: completeness; a full in-place reification of all of System E.

## The two honest limits (unavoidable, write-once)

1. **Faithfulness of the table is human.** Lean can't check that `onCircle ↦ ‖p−o‖²=ρ²` is
   the "right" meaning — that is the one eyeball step. (Few entries → easy.)
2. **The traversal is trusted code.** If it mishandles a connective, translation is wrong;
   it is written and reviewed once.

## Interpretation helpers (`cross`, `dot`) — convention

`collinear`, `circumDet`, `chordForm`, `triArea` route through `cross u v := u.1*v.2 − u.2*v.1`
(2-D cross), and `ℓ` through `dot u v := u.1*v.1 + u.2*v.2`, so the definitions read as the vector
expressions in their comments.  Cost in proofs: after `unfold`ing such a def to hand it to
`ring`/`linarith`, you MUST also `simp only [Prod.fst_sub, Prod.snd_sub]` — because `cross (b-a)(c-a)`
yields `(b-a).1`, which `ring` treats as an atom until the projection is pushed through the
subtraction.  (Symptom if forgotten: opaque `ring failed` with `(p-c).1`-style atoms.)
**When a SECOND proof needs `cross`/`dot`, add `@[simp]` lemmas `cross_eq`/`dot_eq` (the component
form)** so `simp [cross_eq, dot_eq]` does unfold+projection in one step — neutralises the only
recurring friction.  Not needed for one proof.

## Build order

1. Interpretation table (~21 entries).
2. The `Expr` traversal tactic (retargeted `Translator.lean`).
3. Run it on `coincide_equal_area`; prove the ℝ² goal. Use its difficulty as the first
   datapoint on the verdict principle.
4. Then `segment_equal_angle_no_nest`, `segment_arc_crossing`, `segment_superposition`.
