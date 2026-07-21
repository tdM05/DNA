import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step8 (a b c d : Point)
    (hbad : between b a d)
    (h6 : |(d─b)| > |(b─c)|) (h7 : |(d─a)| = |(a─c)|)
    : |(b─a)| + |(a─c)| > |(b─c)| := by
  euclid_finish

end Elements.Book1
