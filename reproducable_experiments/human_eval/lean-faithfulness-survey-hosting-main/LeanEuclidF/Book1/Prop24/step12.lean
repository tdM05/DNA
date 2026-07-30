import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_24_s12
  (b c e f g : Point)
  (h_s10 : |(e─g)| > |(e─f)|)
  (h_s11 : |(e─g)| = |(b─c)|)
  : |(b─c)| > |(e─f)| := by
  linarith

end Elements.Book1
