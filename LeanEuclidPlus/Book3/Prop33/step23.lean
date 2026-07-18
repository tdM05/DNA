import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step23
    (a b d e c₁ c c₂ : Point)
    (h_ab : a ≠ b) (h_da : d ≠ a)
    (h_dab : ∠ d:a:b = ∠ c₁:c:c₂) (hright : ∠ c₁:c:c₂ = ∟)
    (step23_assumption1 : ∠ a:e:b = ∟) :
    ∠ b:a:d = ∠ a:e:b := by
  euclid_finish

end Elements.Book3
