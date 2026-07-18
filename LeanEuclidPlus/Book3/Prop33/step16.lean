import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step16
    (a b d e c₁ c c₂ : Point)
    (h_s14 : ∠ d:a:b = ∠ a:e:b) (h_dab : ∠ d:a:b = ∠ c₁:c:c₂) :
    ∠ c₁:c:c₂ = ∠ a:e:b := by
  euclid_finish

end Elements.Book3
