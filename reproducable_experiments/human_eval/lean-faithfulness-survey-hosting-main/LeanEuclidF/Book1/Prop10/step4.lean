import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_10_s4 (a b c d : Point)
    (hassump1 : |(a─c)| = |(c─b)|)
    (hassump2 : |(c─d)| = |(c─d)|) :
    |(a─c)| = |(b─c)| ∧ |(c─d)| = |(c─d)| := by
  exact ⟨by euclid_finish, hassump2⟩

end Elements.Book1
