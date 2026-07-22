import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step7 (c e g : Point) (EFG : Circle)
    (hcentre : c.isCentre EFG) (heC : e.onCircle EFG) (hgC : g.onCircle EFG) :
    |(c─g)| = |(c─e)| := by
  euclid_apply (point_on_circle_onlyif c e g EFG)
  euclid_finish

end Elements.Book1
