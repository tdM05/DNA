import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_8_s9
  (AB AC DE DF : Line)
  (lineImg : Line → Line)
  (s8 : ¬ (lineImg AB ≠ DE) ∧ ¬ (lineImg AC ≠ DF))
  : lineImg AB = DE ∧ lineImg AC = DF :=
  ⟨Classical.not_not.mp s8.1, Classical.not_not.mp s8.2⟩

end Elements.Book1
