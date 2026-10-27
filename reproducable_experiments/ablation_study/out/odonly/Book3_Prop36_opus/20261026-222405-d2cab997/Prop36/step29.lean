import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step29 (d a c e b : Point)
    (hstep27 : |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─d)| * |(e─d)|)
    (hstep28 : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)|) :
    |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| := by
  rw [hstep27]; exact hstep28.symm

end Elements.Book3
