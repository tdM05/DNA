import SystemE

namespace Elements.Book3

theorem proposition_12 : ∀ (a f g : Point) (ABC ADE : Circle),
  f.isCentre ABC ∧
  g.isCentre ADE ∧
  a.onCircle ABC ∧
  a.onCircle ADE ∧
  ¬ ABC.intersectsCircle ADE ∧
  f.outsideCircle ADE ∧
  g.outsideCircle ABC →
  between f a g := by
  sorry

end Elements.Book3
