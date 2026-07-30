import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_8_s8
  (AB AC DE DF : Line)
  (lineImg : Line → Line)
  (s2 : lineImg AB = DE ∧ lineImg AC = DF)
  : ¬ (lineImg AB ≠ DE) ∧ ¬ (lineImg AC ≠ DF) :=
  ⟨fun h => h s2.1, fun h => h s2.2⟩

end Elements.Book1
