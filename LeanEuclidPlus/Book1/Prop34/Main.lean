import SystemE

namespace Elements.Book1

theorem proposition_34 : ∀ (a b c d : Point) (AB CD AC BD BC : Line),
  formParallelogram a b c d AB CD AC BD ∧ distinctPointsOnLine b c BC →
  |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧
  ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c  = ∠ c:d:b ∧
  Triangle.area △ a:b:c = Triangle.area △ d:c:b := by
  sorry

end Elements.Book1
