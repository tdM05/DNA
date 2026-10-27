import SystemE

namespace Elements.Book3

theorem proposition_4 : ∀ (a b c d e f : Point) (AC BD : Line) (ABCD : Circle),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  f.isCentre ABCD ∧ ¬f.onLine AC ∧ ¬f.onLine BD ∧
  AC ≠ BD ∧ between a e c ∧ between b e d →
  ¬(|(a─e)| = |(e─c)| ∧ |(b─e)| = |(e─d)|) := by
  sorry

end Elements.Book3
