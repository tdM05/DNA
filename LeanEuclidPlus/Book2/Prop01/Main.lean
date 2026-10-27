import SystemE

namespace Elements.Book2


theorem proposition_1 : ∀ (a₁ a₂ b c d e : Point) (A BC : Line),
  distinctPointsOnLine a₁ a₂ A ∧ distinctPointsOnLine b c BC ∧
  d.onLine BC ∧ e.onLine BC ∧ between b d e ∧ between d e c →
  |(a₁─a₂)| * |(b─c)| =
    |(a₁─a₂)| * |(b─d)| + |(a₁─a₂)| * |(d─e)| + |(a₁─a₂)| * |(e─c)| := by
  sorry

end Elements.Book2
