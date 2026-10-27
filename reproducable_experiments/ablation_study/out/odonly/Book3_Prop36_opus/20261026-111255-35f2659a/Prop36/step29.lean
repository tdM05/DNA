import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step29 (a b c d e : Point)
  (step27 : |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─d)| * |(e─d)|)
  (step28 : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)|) :
    |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| := by
  rw [step27, step28]

end Elements.Book3
