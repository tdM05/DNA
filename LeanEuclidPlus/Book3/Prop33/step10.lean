import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step10
    (a b : Point) (α : Circle)
    (h_a_circ : a.onCircle α) (h_b_circ : b.onCircle α) :
    a.onCircle α ∧ b.onCircle α := by
  exact ⟨h_a_circ, h_b_circ⟩

end Elements.Book3
