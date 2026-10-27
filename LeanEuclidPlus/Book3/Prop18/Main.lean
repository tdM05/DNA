import SystemE

namespace Elements.Book3

theorem proposition_18 : ∀ (c f : Point) (ABC : Circle) (DE : Line),
  c.onCircle ABC ∧ c.onLine DE ∧ ¬ DE.intersectsCircle ABC ∧
  f.isCentre ABC ∧ f ≠ c →
  ∀ d : Point, d.onLine DE → d ≠ c → ∠ f:c:d = ∟ := by
  sorry

end Elements.Book3
