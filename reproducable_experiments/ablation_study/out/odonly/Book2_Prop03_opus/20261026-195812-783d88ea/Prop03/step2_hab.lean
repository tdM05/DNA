import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step2_hab (a b c : Point) (CD : Line)
    (hbetween : between a c b)
    (hc_CD : c.onLine CD) :
    ¬(a.sameSide b CD) := by
  euclid_apply (pasch_3 a c b CD)
  euclid_finish

end Elements.Book2
