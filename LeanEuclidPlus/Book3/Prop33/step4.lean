import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step4
    (a b f : Point)
    (h_afb : between a f b) (h_afeq : |(a─f)| = |(f─b)|) :
    between a f b ∧ |(a─f)| = |(f─b)| := by
  exact ⟨h_afb, h_afeq⟩

end Elements.Book3
