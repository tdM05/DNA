import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step7 (a c d : Point)
    (h : |(a─d)| = |(a─c)|) : |(d─a)| = |(a─c)| := by
  euclid_finish

end Elements.Book1
