import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_24_s11
  (b c e g : Point)
  (h_s6 : |(b─c)| = |(e─g)|)
  : |(e─g)| = |(b─c)| :=
  h_s6.symm

end Elements.Book1
