import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_11_s6

  (hassump1 : |(c─d)| = |(c─e)|)
  (hassump2 : |(c─f)| = |(c─f)|)
  : |(c─d)| = |(c─e)| ∧ |(c─f)| = |(c─f)| := by
  exact ⟨hassump1, hassump2⟩

end Elements.Book1
