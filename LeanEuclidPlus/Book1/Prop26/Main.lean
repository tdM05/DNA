import SystemE

namespace Elements.Book1

theorem proposition_26 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (∠ a:b:c = ∠ d:e:f) ∧ (∠ b:c:a = ∠ e:f:d) ∧ (|(b─c)| = |(e─f)| ∨ |(a─b)| = |(d─e)|) →
  (|(a─b)| = |(d─e)|) ∧ (|(b─c)| = |(e─f)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c = ∠ e:d:f) := by
  sorry

end Elements.Book1
