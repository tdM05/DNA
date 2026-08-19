# segment_arc_crossing

## 1. Interpretation (F×F meaning of the symbols this axiom uses)
Point = `(x,y) ∈ F²`, F a Euclidean field.
- **`CircularSegment.inside` / `.outside`:** TODO — region containment of one segment in another (common chord, same side).
- **`formCircularSegment`:** abbrev over existing predicates (see other files).

## 2. Statement
TODO — paste from `SystemE/Theory/Inferences/Diagrammatic.lean`.

## 3. Proof (true in every F×F under §1)
TODO. "Neither inside nor outside" ⟹ arcs cross ⟹ shared point g ≠ c,d.
⚠ HIGH RISK: this is an intermediate-value / continuity statement, and IVT FAILS in a general
(non-complete) Euclidean field. Must check the crossing point g is CONSTRUCTIBLE (a √ of field data,
so it exists in F) rather than requiring completeness. If it needs completeness → UNSOUND over general
F and must be restated.
STATUS: CONJECTURED — HIGH RISK.
