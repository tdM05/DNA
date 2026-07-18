import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step41
    (a b d h c₁ c c₂ : Point)
    (h_s39 : ∠ b:a:d = ∠ a:h:b) (h_s40 : ∠ b:a:d = ∠ c₁:c:c₂) :
    ∠ a:h:b = ∠ c₁:c:c₂ := by
  euclid_finish

end Elements.Book3
