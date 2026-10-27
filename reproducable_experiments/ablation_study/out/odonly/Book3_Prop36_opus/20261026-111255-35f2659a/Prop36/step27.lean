import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step27 (a b c d e : Point)
  (step25 : |(d─a)| * |(d─c)| + |(e─c)| * |(e─c)| = |(e─d)| * |(e─d)|)
  (step26 : |(e─c)| = |(e─b)|) :
    |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─d)| * |(e─d)| := by
  rw [← step26]; exact step25

end Elements.Book3
