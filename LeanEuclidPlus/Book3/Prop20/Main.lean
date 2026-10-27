import SystemE

namespace Elements.Book3

theorem proposition_20 : ∀ (a b c e : Point) (BC : Line) (ABC : Circle),
  e.isCentre ABC ∧
  a.onCircle ABC ∧
  b.onCircle ABC ∧
  c.onCircle ABC ∧
  distinctPointsOnLine b c BC ∧
  b ≠ a ∧
  c ≠ a ∧
  a.sameSide e BC →
  ∠ b:e:c = ∠ b:a:c + ∠ b:a:c := by
  sorry

end Elements.Book3
