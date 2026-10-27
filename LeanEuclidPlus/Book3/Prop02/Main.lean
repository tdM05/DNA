import SystemE

namespace Elements.Book3

theorem proposition_2 : ∀ (a b : Point) (ABC : Circle),
  a.onCircle ABC ∧ b.onCircle ABC ∧ a ≠ b →
  ∀ p : Point, between a p b → p.insideCircle ABC := by
  sorry

end Elements.Book3
