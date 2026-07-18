import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step15
    (a b d c₁ c c₂ : Point)
    (h_dab : ∠ d:a:b = ∠ c₁:c:c₂) :
    ∠ d:a:b = ∠ c₁:c:c₂ := by
  exact h_dab

end Elements.Book3
