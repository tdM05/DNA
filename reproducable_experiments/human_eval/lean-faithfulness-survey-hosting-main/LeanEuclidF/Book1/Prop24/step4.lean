import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_24_s4

  (hassump1 : |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─g)|)
  : |(b─a)| = |(e─d)| ∧ |(a─c)| = |(d─g)| := by
  exact ⟨by euclid_finish, hassump1.2⟩

end Elements.Book1
