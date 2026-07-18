import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step11
    (g a b e : Point) (α : Circle)
    (h_g_centre : g.isCentre α) (h_a_circ : a.onCircle α)
    (h_b_circ : b.onCircle α) (h_e_circ : e.onCircle α) :
    g.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ e.onCircle α := by
  exact ⟨h_g_centre, h_a_circ, h_b_circ, h_e_circ⟩

end Elements.Book3
