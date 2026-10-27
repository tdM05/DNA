import SystemE

namespace Elements.Book3


theorem proposition_17 : ∀ (a : Point) (BCD : Circle),
  a.outsideCircle BCD →
  ∃ L : Line, a.onLine L ∧ (∃ p : Point, p.onLine L ∧ p.onCircle BCD) ∧ ¬ L.intersectsCircle BCD := by
  sorry

end Elements.Book3
