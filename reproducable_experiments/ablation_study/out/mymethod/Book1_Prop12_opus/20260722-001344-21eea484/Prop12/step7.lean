import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step7 (c e g : Point) (EFG : Circle)
    (hc : c.isCentre EFG) (he : e.onCircle EFG) (hg : g.onCircle EFG) :
    |(c─g)| = |(c─e)| := by
  euclid_finish

end Elements.Book1
