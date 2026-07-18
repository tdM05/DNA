import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step42
    (a b h c₁ c c₂ : Point) (α : Circle)
    (h_a_circ : a.onCircle α) (h_b_circ : b.onCircle α) (h_h_circ : h.onCircle α)
    (h_s41 : ∠ a:h:b = ∠ c₁:c:c₂) :
    ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂ := by
  exact ⟨α, h, h_a_circ, h_b_circ, h_h_circ, h_s41⟩

end Elements.Book3
