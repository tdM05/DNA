import SystemE

namespace Elements.Book3

theorem proposition_16 : ∀ (a b d e : Point) (ABC : Circle) (AE : Line),
    d.isCentre ABC ∧
    a.onCircle ABC ∧ b.onCircle ABC ∧ between a d b ∧
    distinctPointsOnLine a e AE ∧
    ∠ e:a:b = ∟ →
    ((∃ p : Point, p.onLine AE ∧ p.onCircle ABC) ∧ ¬ AE.intersectsCircle ABC) ∧
    (∀ (FA : Line), a.onLine FA → FA ≠ AE → FA.intersectsCircle ABC) := by
  sorry

end Elements.Book3
