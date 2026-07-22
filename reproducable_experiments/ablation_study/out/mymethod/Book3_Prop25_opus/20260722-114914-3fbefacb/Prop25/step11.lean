import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step11 (a c d e : Point)
    (hassump1 : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟) :
    ∠ a:d:e = ∠ c:d:e := by
  obtain ⟨h1, h2⟩ := hassump1
  rw [h1, h2]

end Elements.Book3
