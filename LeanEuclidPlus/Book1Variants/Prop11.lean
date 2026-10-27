import SystemE

namespace Elements.Book1

theorem proposition_11' : ∀ (a b c x : Point) (AB : Line),
  (distinctPointsOnLine a b AB) ∧ (between a c b) ∧ ¬(x.onLine AB) →
  exists f : Point, (f.sameSide x AB) ∧ (∠ a:c:f = ∟) := by
  sorry

theorem proposition_11'' : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  exists (f : Point), ¬(f.onLine AB) ∧ (∠ f:a:b = ∟) := by
  sorry

theorem proposition_11''' : ∀ (a b x : Point) (AB : Line),
  ¬(x.onLine AB) ∧ (distinctPointsOnLine a b AB) →
  exists (f : Point), ¬(f.onLine AB) ∧ (f.opposingSides x AB) ∧ (∠ f:a:b = ∟) := by
  sorry

end Elements.Book1
