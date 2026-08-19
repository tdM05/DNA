# III.24 — new objects / axioms status

## New vocabulary added (SystemE)
- `CircularSegment` sort + `⌓` area (`Sorts/CircularSegments.lean`)
- `Arc` sort + `⌒` measure (`Sorts/Arcs.lean`)
- `CircularSegment.inside` / `.outside` relations + `formCircularSegment` (`Relations.lean`)
- `segment_superposition` axiom (`Inferences/Superposition.lean`) — the motion: places A→C, lays AB
  along CD, preserves chord/inscribed-angle/AREA, returns image points a' e' b' + image circle AEB'
  with `formCircularSegment a' e' b' CD AEB'`.
- `segment_arc_crossing` axiom (`Inferences/Diagrammatic.lean`) — the "miss" case: two co-chordal
  same-side segments, neither inside nor outside ⟹ their circles share a third point g (≠ c,d).
  Sound (constrained to arcs on a common chord/side, where neither-nested forces a crossing).

## Step status

PROVABLE ✅ (Phase-B wiring only, System E sufficient):
- **hImgCircle** — RESOLVED, folded into `segment_superposition` (`formCircularSegment a' e' b' CD AEB'`).
- **step1** `ImgSegment b = d` — from superposition outputs + |ab|=|cd|.
- **step2** — reductio (habsurd1) + double-negation.
- **step3** trichotomy `inside ∨ outside ∨ (¬inside ∧ ¬outside)` — classical tautology.
- **step4** `(¬inside ∧ ¬outside) → ∃ 3 shared points` — via `segment_arc_crossing`: gives g on both
  circles ≠ c,d; then {c=ImgSegment a, d=ImgSegment b, g} are the 3 shared points.
- **step6/step7** reductio close — pure logic.
- **step8** `⌓ a:e:b = ⌓ c:f:d` — from `segment_superposition`'s `⌓ a':e':b' = ⌓ a:e:b` + coincidence.

- **step5** `False` — closes once the nesting branches are excluded (below), then step3 collapses to
  the miss disjunct → step4 → 3 points → III.10.
- **`hnot_inside` / `hnot_outside`** (obligations in Main.lean between step3 and step4: the moved
  segment doesn't nest in/around CFD) — via the added axiom `segment_equal_angle_no_nest`: the moved
  segment has `∠ = ∠c:f:d` (from `segment_superposition`'s angle-preservation + the hypothesis
  `∠a:e:b = ∠c:f:d`), and equal inscribed angle on a common chord/side ⟹ no nesting.

Note: Euclid cites ONLY III.10 + C.N.4; he applies "cut at >2 points [III.10]" to all three branches,
but III.10 genuinely covers only the crossing (miss) case. The inside/outside branches are Euclid's
looseness — `segment_equal_angle_no_nest` fills them using his own (unused) equal-angle hypothesis.

## Bottom line
All steps provable with the current System E. Three added axioms carry III.24:
`segment_superposition` (motion), `segment_arc_crossing` (miss → III.10), `segment_equal_angle_no_nest`
(excludes nesting). No III.23 citation needed.
