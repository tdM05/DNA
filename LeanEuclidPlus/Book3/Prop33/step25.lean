import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step25
    (a b d e c₁ c c₂ : Point)
    (h_s23 : ∠ b:a:d = ∠ a:e:b) (h_s24 : ∠ b:a:d = ∠ c₁:c:c₂) :
    ∠ a:e:b = ∠ c₁:c:c₂ := by
  euclid_finish

end Elements.Book3
