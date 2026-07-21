import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step6 (GK : Line) (a c d k : Point)
  (hca_ss : c.sameSide a GK) (hk_gk : k.onLine GK) (hckd : between c k d) :
  a.opposingSides d GK := by euclid_finish

end Elements.Book1
