# segment_equal_angle_no_nest

## 1. Interpretation (F×F meaning of the symbols this axiom uses)
Point = `(x,y) ∈ F²`, F a Euclidean field. `∠a:b:c` = existing cartesian meaning.
- **`CircularSegment.inside` / `.outside`:** TODO — region containment (common chord, same side).
- **`formCircularSegment`:** abbrev over existing predicates.

## 2. Statement
TODO — paste from `SystemE/Theory/Inferences/Diagrammatic.lean`.

## 3. Proof (true in every F×F under §1)
TODO. Inscribed-angle theorem in F²: on fixed chord c–d and side, ∠c:·:d strictly determines the
circle ⟹ equal inscribed angle ⟹ same circle ⟹ same region ⟹ neither inside nor outside.
Check: inscribed-angle theorem is algebraic (holds over general Euclidean field); verify the
strict-monotone step uses no order-completeness.
STATUS: CONJECTURED.
