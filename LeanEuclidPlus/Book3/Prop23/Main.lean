import SystemE

namespace Elements.Book3

theorem proposition_23 : ∀ (a b c d : Point) (AB : Line) (ACB ADB : Circle),
  distinctPointsOnLine a b AB ∧
  a.onCircle ACB ∧ b.onCircle ACB ∧ c.onCircle ACB ∧
  a.onCircle ADB ∧ b.onCircle ADB ∧ d.onCircle ADB ∧
  c.sameSide d AB ∧
  between a c d ∧
  ∠ a:c:b = ∠ a:d:b ∧
  ACB ≠ ADB →
  False := by
  sorry

end Elements.Book3
