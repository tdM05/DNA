import SystemE

namespace Elements.Book3

open Elements.Book1

theorem proposition_35 : ∀ (a b c d e : Point) (ABCD : Circle),
    a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
    between a e c ∧ between b e d →
    |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)| := by
  sorry

end Elements.Book3
