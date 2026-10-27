import SystemE

namespace Elements.Book3

theorem proposition_15 : ∀ (a b c d e f g h k : Point) (ABCD : Circle) (BC FG : Line),
  e.isCentre ABCD ∧
  a.onCircle ABCD ∧ d.onCircle ABCD ∧ between a e d ∧
  b.onCircle ABCD ∧ c.onCircle ABCD ∧ distinctPointsOnLine b c BC ∧
  f.onCircle ABCD ∧ g.onCircle ABCD ∧ distinctPointsOnLine f g FG ∧
  h.onLine BC ∧ ∠ e:h:b = ∟ ∧ e ≠ h ∧ h ≠ b ∧
  k.onLine FG ∧ ∠ e:k:f = ∟ ∧ k ≠ f ∧
  |(e─h)| < |(e─k)| →
  |(a─d)| > |(b─c)| ∧ |(b─c)| > |(f─g)| := by
  sorry

end Elements.Book3
