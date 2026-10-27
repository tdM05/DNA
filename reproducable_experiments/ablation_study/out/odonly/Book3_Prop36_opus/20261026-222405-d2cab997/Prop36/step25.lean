import SystemE
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step25 (d a c e f : Point)
    (hstep22 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| = |(f─d)| * |(f─d)| + |(e─f)| * |(e─f)|)
    (hstep23 : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)|)
    (hstep24 : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)|) :
    |(d─a)| * |(d─c)| + |(e─c)| * |(e─c)| = |(e─d)| * |(e─d)| := by
  have hsd : |(d─f)| = |(f─d)| := by euclid_finish
  have hse : |(f─e)| = |(e─f)| := by euclid_finish
  rw [hsd, hse] at hstep24
  linarith [hstep22, hstep23, hstep24]

end Elements.Book3
