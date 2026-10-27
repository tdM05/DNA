import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step6 (c e g h : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(g─h)| = |(h─e)|)   -- "$GH$ is equal to $HE$"
  (hassump2 : |(h─c)| = |(h─c)|)   -- "$HC$ (is) common"
  : |(g─h)| = |(e─h)| ∧ |(h─c)| = |(h─c)| := by
  euclid_finish

end Elements.Book1
