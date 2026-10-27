import SystemE

namespace Elements.Book1

theorem proposition_46' : ∀ (a b x : Point) (AB : Line), ¬(x.onLine AB) ∧ distinctPointsOnLine a b AB →
  ∃ (d e : Point) (DE AD BE : Line), d.opposingSides x AB ∧ formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
  (∠ b:a:d : ℝ) = ∟ ∧ (∠ a:d:e : ℝ) = ∟ ∧ (∠ a:b:e : ℝ) = ∟ ∧ (∠ b:e:d : ℝ) = ∟ := by
  sorry

end Elements.Book1
