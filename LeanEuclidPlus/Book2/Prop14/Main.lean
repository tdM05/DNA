import SystemE

namespace Elements.Book2


/-!
Prop 2.14 — quadrature: "To construct a square equal to a given rectilinear figure A."

Modeling: System E has no general rectilinear-figure type; area is `Triangle.area` and a polygon is a
sum of triangle areas (as Prop 1.45 does). Euclid's text cites **[Prop. 1.45]** ("construct a
parallelogram equal to a given rectilinear figure"), so the given figure A is modeled as a
QUADRILATERAL `a b c q` (the smallest figure to which 1.45 genuinely applies), with diagonal `QB`
splitting it into triangles `a:b:q` and `q:b:c`; its area is `△ a:b:q + △ q:b:c`. Step 1 builds the
right-angled parallelogram BD via **Prop 1.45**. Rectangle corners: `b₀ = B`, `e = E`, `d = D`,
`c₀ = C` (right angle at `b₀`); `b₀, c₀` are subscripted to avoid clashing with `a b c`, and A's 4th
vertex is `q` (not `d`) to avoid clashing with the rectangle's `d = D`.

Structure: Euclid splits on whether BE = ED. If equal, the rectangle BD is already the required
square and the construction is complete (2.14.2). If not, one of BE, ED is greater and the
geometric-mean construction produces the side EH (2.14.3–2.14.21). Both branches close the goal
with their own witness — the case split is genuine, mirroring Euclid's two cases.
-/

theorem proposition_14 : ∀ (a b c q : Point) (AB BC CQ AQ QB : Line),
  formTriangle a b q AB QB AQ ∧ formTriangle b c q BC CQ QB ∧ a.opposingSides c QB →
  ∃ (e h : Point),
    |(e─h)| * |(e─h)| = Triangle.area △ a:b:q + Triangle.area △ q:b:c := by
  sorry

end Elements.Book2
