import SystemE

namespace Elements.Book1

theorem proposition_23' : ∀ (a b c d e x : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE ∧ ¬(x.onLine AB) →
  ∃ f : Point, f ≠ a ∧ (f.onLine AB ∨ f.sameSide x AB) ∧ (∠ f:a:b = ∠ d:c:e) := by
  sorry

end Elements.Book1
