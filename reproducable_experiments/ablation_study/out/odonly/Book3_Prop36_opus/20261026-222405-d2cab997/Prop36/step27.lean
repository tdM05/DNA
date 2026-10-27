import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step27 (d a c e b : Point)
    (hstep25 : |(d─a)| * |(d─c)| + |(e─c)| * |(e─c)| = |(e─d)| * |(e─d)|)
    (hstep26 : |(e─c)| = |(e─b)|) :
    |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─d)| * |(e─d)| := by
  rw [← hstep26]; exact hstep25

end Elements.Book3
