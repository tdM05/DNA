import SystemE

namespace Elements.Book3

theorem proposition_8 : ∀ (ABC : Circle) (m d a e f c g k l h : Point) (AG : Line),
  m.isCentre ABC →
  d.outsideCircle ABC →
  -- Diameter: G convex (near, between D and center), A concave (far, beyond center from D)
  a.onCircle ABC →
  g.onCircle ABC →
  distinctPointsOnLine a g AG →
  d.onLine AG →
  between d g m →
  between g m a →
  -- Concave-arc points: E, F, C — each has a convex (near) partner between D and it on the same line
  e.onCircle ABC → (∃ en : Point, en.onCircle ABC ∧ between d en e) →
  f.onCircle ABC → (∃ fn : Point, fn.onCircle ABC ∧ between d fn f) →
  c.onCircle ABC → (∃ cn : Point, cn.onCircle ABC ∧ between d cn c) →
  -- Convex-arc points: K, L, H — each has a concave (far) partner beyond it from D on the same line
  k.onCircle ABC → (∃ kf : Point, kf.onCircle ABC ∧ between d k kf) →
  l.onCircle ABC → (∃ lf : Point, lf.onCircle ABC ∧ between d l lf) →
  h.onCircle ABC → (∃ hf : Point, hf.onCircle ABC ∧ between d h hf) →
  -- Non-degeneracy: concave arc points ≠ far endpoint; c also ≠ near endpoint g (not angle-derivable)
  e ≠ a → f ≠ a → c ≠ a → c ≠ g →
  k ≠ g → l ≠ g → h ≠ g →
  -- Angle ordering at M for concave lines (nearer to DA = larger angle at M)
  ∠ e:m:d > ∠ f:m:d → ∠ f:m:d > ∠ c:m:d →
  -- Angle ordering at M for convex lines (nearer to DG = smaller angle at M)
  ∠ k:m:d < ∠ l:m:d → ∠ l:m:d < ∠ h:m:d →
  -- Same-side condition for convex arc: k and l on same side of diameter AG (figure-reading)
  l.sameSide k AG →
  -- (1) CONCAVE: DA is the greatest line to the concave arc; nearer-to-DA is greater
  ( |(d─a)| > |(d─e)| ∧ |(d─e)| > |(d─f)| ∧ |(d─f)| > |(d─c)| ) ∧
  -- (2) CONVEX: DG is the least line to the convex arc; nearer-to-DG is less
  ( |(d─g)| < |(d─k)| ∧ |(d─k)| < |(d─l)| ∧ |(d─l)| < |(d─h)| ) ∧
  -- (3) Exactly two equal lines from D to the circle, one each side of DG: DK and its angle-mirror DB
  ∃ b : Point, b.onCircle ABC ∧ b.opposingSides k AG ∧ |(d─b)| = |(d─k)| ∧
    ∀ n : Point, n.onCircle ABC → |(d─n)| = |(d─k)| → n = k ∨ n = b := by
  sorry

end Elements.Book3
