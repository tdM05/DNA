import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_6_s3 (a b c d : Point) (hbtw : between b d a) (heq : |(b─d)| = |(a─c)|) :
    between b d a ∧ |(b─d)| = |(a─c)| := by
  exact ⟨hbtw, heq⟩

end Elements.Book1
