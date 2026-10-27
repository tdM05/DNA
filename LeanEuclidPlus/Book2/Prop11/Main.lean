import SystemE

namespace Elements.Book2

open Elements.Book1

theorem proposition_11 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ h : Point, between a h b ∧
    |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| := by
  sorry

end Elements.Book2
