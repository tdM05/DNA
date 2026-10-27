import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step7_cnd (a b c d : Point)
    (hbetween : between a c b)
    (h_cd_cb : |(c─d)| = |(c─b)|) :
    c ≠ d := by
  euclid_finish

end Elements.Book2
