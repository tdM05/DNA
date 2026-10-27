import SystemE

namespace Elements.Book3

theorem proposition_21 : ∀ (a b d e : Point) (BD : Line) (ABCD : Circle),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ d.onCircle ABCD ∧ e.onCircle ABCD ∧
  distinctPointsOnLine b d BD ∧
  a.sameSide e BD →
  ∠ b:a:d = ∠ b:e:d := by
  sorry

end Elements.Book3
