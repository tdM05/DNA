import SystemE

namespace Elements.Book3

open Elements.Book1

theorem proposition_33 : ∀ (a b c₁ c c₂ : Point),
  a ≠ b →
  c₁ ≠ c → c ≠ c₂ →
  0 < ∠ c₁:c:c₂ → ∠ c₁:c:c₂ < ∟ + ∟ →
  ∃ (α : Circle) (e : Point), a.onCircle α ∧ b.onCircle α ∧ e.onCircle α ∧ ∠ a:e:b = ∠ c₁:c:c₂ := by
  sorry

end Elements.Book3
