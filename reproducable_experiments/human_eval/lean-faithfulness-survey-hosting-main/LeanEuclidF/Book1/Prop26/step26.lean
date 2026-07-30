import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_26_s26
    (h : Point)
    (hassump1 : |(b─h)| = |(e─f)|)
    (hassump2 : |(a─b)| = |(d─e)|) :
    |(a─b)| = |(d─e)| ∧ |(b─h)| = |(e─f)| :=
  ⟨hassump2, hassump1⟩

end Elements.Book1
