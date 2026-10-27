import SystemE

namespace Elements.Book1

theorem proposition_20 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC →
  |(b─a)| + |(a─c)| > |(b─c)| ∧
  |(a─b)| + |(b─c)| > |(a─c)| ∧
  |(b─c)| + |(c─a)| > |(a─b)| := by
  sorry

end Elements.Book1
