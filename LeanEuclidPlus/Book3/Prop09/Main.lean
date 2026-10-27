import SystemE

namespace Elements.Book3

open Elements.Book1

theorem proposition_9 : ∀ (ABC : Circle) (a b c d : Point),
    d.insideCircle ABC ∧
    a.onCircle ABC ∧ b.onCircle ABC ∧ c.onCircle ABC ∧
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| →
    d.isCentre ABC := by
  sorry

end Elements.Book3
