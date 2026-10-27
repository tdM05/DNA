import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step25
  (a c d e f : Point)
  (step22 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| = |(f─d)| * |(f─d)| + |(e─f)| * |(e─f)|)
  (step23 : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)|)
  (step24 : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)|)
  : |(d─a)| * |(d─c)| + |(e─c)| * |(e─c)| = |(e─d)| * |(e─d)| := by
  have sq1 : |(d─f)| * |(d─f)| = |(f─d)| * |(f─d)| := by rw [segment_symmetric d f]
  have sq2 : |(f─e)| * |(f─e)| = |(e─f)| * |(e─f)| := by rw [segment_symmetric f e]
  linarith [step22, step23, step24, sq1, sq2]

end Elements.Book3
