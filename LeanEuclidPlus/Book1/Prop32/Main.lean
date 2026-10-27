import SystemE

namespace Elements.Book1

theorem proposition_32 : ∀ (a b c d : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (between b c d) →
  ∠ a:c:d = ∠ c:a:b + ∠ a:b:c ∧
  ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟ := by
  sorry

end Elements.Book1
