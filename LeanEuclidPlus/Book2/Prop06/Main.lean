import SystemE

namespace Elements.Book2


theorem proposition_6 : ∀ (a b c d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧
  between a c b ∧ |(a─c)| = |(c─b)| ∧ between a b d →
  |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| := by
  sorry

end Elements.Book2
