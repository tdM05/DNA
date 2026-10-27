import SystemE

namespace Elements.Book3

open Elements.Book1

theorem proposition_34 : ∀ (ABC : Circle) (d1 d d2 : Point),
  d1 ≠ d ∧ d2 ≠ d →
  0 < ∠ d1:d:d2 → ∠ d1:d:d2 < ∟ + ∟ →
  ∃ (b c : Point), b.onCircle ABC ∧ c.onCircle ABC ∧ b ≠ c ∧
    ∃ a : Point, a.onCircle ABC ∧ ∠ b:a:c = ∠ d1:d:d2 := by
  sorry

end Elements.Book3
