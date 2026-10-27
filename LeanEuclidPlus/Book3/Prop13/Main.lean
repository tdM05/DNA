import SystemE

namespace Elements.Book3

theorem proposition_13 : ∀ (ABDC EBFD : Circle),
  ABDC ≠ EBFD ∧ (∃ d : Point, d.onCircle ABDC ∧ d.onCircle EBFD) ∧ ¬ ABDC.intersectsCircle EBFD →
  ∀ (d b : Point), d.onCircle ABDC ∧ d.onCircle EBFD ∧ b.onCircle ABDC ∧ b.onCircle EBFD → d = b := by
  sorry

end Elements.Book3
