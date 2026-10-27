import SystemE

namespace Elements.Book1

theorem proposition_12 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(c.onLine AB) →
  exists h : Point, h.onLine AB ∧ (∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) ∧
    (∀ (p : Point), p.onLine AB → p ≠ h → ∠ p:h:c = ∟) := by
  sorry

end Elements.Book1
