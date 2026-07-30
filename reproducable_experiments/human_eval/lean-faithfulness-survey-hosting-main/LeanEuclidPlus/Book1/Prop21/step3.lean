import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_21_s3 (a b c e : Point)
    (hstep2 : |(a─b)| + |(a─e)| > |(b─e)|) :
    |(a─b)| + |(a─e)| + |(e─c)| > |(b─e)| + |(e─c)| := by
  linarith

end Elements.Book1
