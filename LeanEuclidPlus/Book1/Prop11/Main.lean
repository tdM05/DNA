import SystemE

namespace Elements.Book1
-- map done
theorem proposition_11 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  exists f : Point, ¬(f.onLine AB) ∧ (∠ a:c:f = ∟) := by
  sorry

end Elements.Book1
