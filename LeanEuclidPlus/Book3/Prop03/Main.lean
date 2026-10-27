import SystemE

namespace Elements.Book3

theorem proposition_3 : ∀ (a b e f : Point) (ABC : Circle) (AB CD : Line),
  a.onCircle ABC ∧ b.onCircle ABC ∧ distinctPointsOnLine a b AB ∧
  e.isCentre ABC ∧ e.onLine CD ∧ ¬e.onLine AB ∧
  f.onLine AB ∧ f.onLine CD ∧ between a f b →
  (|(a─f)| = |(f─b)| → ∠ a:f:e = ∟) ∧
  (∠ a:f:e = ∟ → |(a─f)| = |(f─b)|) := by
  sorry

end Elements.Book3
