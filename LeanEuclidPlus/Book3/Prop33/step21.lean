import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step21
    (f a b : Point) (α : Circle)
    (h_f_centre : f.isCentre α) (h_a_circ : a.onCircle α) (h_b_circ : b.onCircle α) :
    f.isCentre α ∧ a.onCircle α ∧ b.onCircle α := by
  exact ⟨h_f_centre, h_a_circ, h_b_circ⟩

end Elements.Book3
