import SystemE

namespace Elements.Book3

theorem proposition_11 : ∀ (a f g : Point) (ABC ADE : Circle),
  a.onCircle ABC ∧ a.onCircle ADE ∧
  ¬ ABC.intersectsCircle ADE ∧
  g.insideCircle ABC ∧
  |(g─a)| < |(f─a)| ∧
  f.isCentre ABC ∧ g.isCentre ADE ∧
  f ≠ g →
  between f g a := by
  sorry

end Elements.Book3
