# III.24 — new objects / axioms needed

## New vocabulary already added
- `CircularSegment` sort + `⌓` area (`Sorts/CircularSegments.lean`)
- `CircularSegment.inside` / `.outside` relations (`Relations.lean`)

## Steps needing attention

**hImgCircle (segment→circle)** — deferred `have`. Euclid superposes the SEGMENT; the
contradiction needs its CIRCLE. Need a link "the arc of a segment lies on a circle" so
`ImgCircle AEB` is justified, not conjured. → new relation `CircularSegment → Circle → Prop`,
or fold into the superposition axiom.

**step1 `ImgSegment b = d`** — needs the superposition INFERENCE (the big axiom): rigid motion
placing A→C, AB along CD, preserving length. Circle/segment analogue of `axiom superposition`.
Produces `ImgSegment`, `ImgCircle`, and their licensed facts (placement, length, congruent copy).

**step3 `inside ∨ outside ∨ miss`** — needs the trichotomy provable: inside/outside/miss
exhaust the cases for a segment vs. a segment on the same chord. Likely an axiom about
`inside`/`outside`.

**step4 (@euclid_gap) `miss → >2 shared points`** — THE gap. "miss ⟹ third common point" plus
the silent segment→circle move. Only the crossing case is refuted by III.10; needs the
figure-read that miss yields a third point (deferred / axiom); inside/outside are left unhandled
by Euclid.

**step8 `⌓ a:e:b = ⌓ c:f:d`** — C.N.4 "coincide ⟹ equal". Needs coincidence (step7) +
"superposition preserves segment area" (`⌓ (ImgSegment a):(ImgSegment e):(ImgSegment b) = ⌓ a:e:b`,
dropped from hsup) ⟹ equal areas.

## Summary of additions
1. Superposition inference for segments (returns ImgSegment, ImgCircle + facts). [big]
2. segment→circle relation (arc lies on a circle).
3. inside/outside/miss trichotomy + area-congruence-under-coincidence (C.N.4).
