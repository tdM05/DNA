import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_33_s3
  (a b c d : Point)
  (hassump1 : |(a─b)| = |(c─d)|)
  (hassump2 : |(b─c)| = |(b─c)|)
  (s2 : ∠ a:b:c = ∠ b:c:d)
  : (|(a─b)| = |(d─c)| ∧ |(b─c)| = |(c─b)|) ∧ ∠ a:b:c = ∠ b:c:d := by
  exact ⟨⟨by euclid_finish, by euclid_finish⟩, s2⟩

end Elements.Book1
