import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step3 (a b c d : Point)
  (h_bet : between b d a) (h_len : |(b─d)| = |(a─c)|)
  : between b d a ∧ |(b─d)| = |(a─c)| := by exact ⟨h_bet, h_len⟩

end Elements.Book1
