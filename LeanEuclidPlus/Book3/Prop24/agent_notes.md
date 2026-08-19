# Book3/Prop24 — agent notes

## Status: Phase B COMPLETE (all 12 nodes `--all`-certified, 2026-08-13). Ready for Phase C (human `wire_main.py`).

## Two things had to change to make the map provable (both authorized by human):

1. **Construction frame was unprovable as mapped.** The map had opaque deferred maps
   `have ImgSegment : Point → Point := by sorry` / `have ImgCircle : Circle → Circle := by sorry` /
   `have hImgCircle := by sorry`. An opaque sorry'd function carries NO facts, so `ImgSegment a = c`
   etc. are unprovable in principle. FIX (Prop04 `ptImg` pattern): `euclid_apply (segment_superposition
   a e b c d f AB CD AEB) as (a', e', b', AEB')` then concrete `let ImgSegment/ImgCircle` built from
   the outputs. No euclid_sentence claim type changed. NOTE: derive all distinctness (e≠a, b≠a, b≠e)
   and the onCircle anchors BEFORE the function `let`s — a `Point→Point` local in context crashes the
   SMT translator behind `euclid_finish` ("Expected geometric object, got ([anonymous], …)").

2. **step8 needed one missing axiom** (the C.N.4 close). Goal `⌓a:e:b = ⌓c:f:d` reduces (via
   superposition's `⌓a':e':b'=⌓a:e:b` + a'=c, b'=d) to `⌓c:e':d = ⌓c:f:d` — coincident segments
   (same circle CFD, same chord CD, arc pts e'/f same side) have equal area. The only ⌓-area axiom
   was superposition; `CSegPPP` is otherwise fully opaque in the SMT theory. Human ADDED:
   `CircularSegment.coincides` (Relations.lean) + `coincide_equal_area : ∀ s t, s.coincides t →
   (s:ℝ)=(t:ℝ)` (Diagrammatic.lean). Sound (arc between c,d on one side is unique), C.N.4-level, NOT
   III.24-in-disguise (same circle/chord, fires only after coincidence established).

## Proof shape (all TERM-MODE for the segment machinery — inside/outside/⌓ are opaque to euclid_finish):
- step2 (crux coincidence) & step5 (III.10 False): no-nest (`segment_equal_angle_no_nest`) →
  arc-crossing (`segment_arc_crossing`) → 3 shared pts → `proposition_10` (III.10). step5 must use
  `euclid_apply (proposition_10 …)` (NO `as`) then `absurd` — criterion-3 records the citation only
  via euclid_apply, and `as` won't bind a `¬∃` conclusion.
- hnot_inside/hnot_outside: `segment_equal_angle_no_nest` `.1`/`.2`.
- step3: classical trichotomy p∨q∨(¬p∧¬q). step6/step7: reductio close + not_not. step8: C.N.4 axiom.
- CircularSegment binders: the tooling only accepts Point/Line/Circle object binders — state `mseg`/
  `tseg` conclusions in unfolded `CircularSegment.ofPoints …` form, not as CircularSegment params.
