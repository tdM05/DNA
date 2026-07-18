import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step19
    (a b d c₁ c c₂ : Point)
    (h_ab : a ≠ b) (h_da : d ≠ a)
    (h_dab : ∠ d:a:b = ∠ c₁:c:c₂) :
    ∠ b:a:d = ∠ c₁:c:c₂ := by
  euclid_finish

end Elements.Book3
