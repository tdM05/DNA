import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step6 (a c d k : Point) (CD GK : Line)
  (hc_CD : c.onLine CD) (hd_CD : d.onLine CD) (hk_GK : k.onLine GK)
  (hc_ss : c.sameSide a GK) (hckd : between c k d) :
  a.opposingSides d GK := by
  euclid_finish

end Elements.Book1
