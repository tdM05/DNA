import SystemE

namespace Elements.Book3

theorem proposition_14 : ∀ (a b c d e f g : Point) (ABDC : Circle) (AB CD : Line),
  a.onCircle ABDC ∧ b.onCircle ABDC ∧ c.onCircle ABDC ∧ d.onCircle ABDC ∧
  e.isCentre ABDC ∧
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧
  f.onLine AB ∧ ∠ a:f:e = ∟ ∧ between a f b ∧
  g.onLine CD ∧ ∠ c:g:e = ∟ ∧ between c g d →
  (|(a─b)| = |(c─d)| → |(e─f)| = |(e─g)|) ∧
  (|(e─f)| = |(e─g)| → |(a─b)| = |(c─d)|) := by
  sorry

end Elements.Book3
