import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_1_s1 (a b : Point) (BCD : Circle)
    (hc : a.isCentre BCD) (hb : b.onCircle BCD) :
    a.isCentre BCD ∧ b.onCircle BCD := by
  exact ⟨hc, hb⟩

end Elements.Book1
