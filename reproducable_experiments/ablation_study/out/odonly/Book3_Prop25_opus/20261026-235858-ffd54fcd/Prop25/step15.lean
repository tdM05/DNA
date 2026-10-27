import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step15 (a b c e : Point)
    (hstep13 : |(a─e)| = |(b─e)|) (hstep14 : |(b─e)| = |(c─e)|) :
    |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)| := by
  euclid_finish

end Elements.Book3
