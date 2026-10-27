import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step14 (a b c e : Point)
    (hstep12 : |(a─e)| = |(c─e)|) (hstep13 : |(a─e)| = |(b─e)|) :
    |(b─e)| = |(c─e)| := by
  euclid_finish

end Elements.Book3
