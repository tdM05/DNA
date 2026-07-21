import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step6 (GK CD EF : Line) (a c d k h : Point)
  (hc_CD : c.onLine CD) (hd_CD : d.onLine CD) (hk_CD : k.onLine CD) (hk_GK : k.onLine GK)
  (hckd : between c k d) (hc_ss : c.sameSide a GK)
  (hh_EF : h.onLine EF) (hh_GK : h.onLine GK)
  (hCDEF : CD ≠ EF) (hCDEF_int : ¬CD.intersectsLine EF) :
    a.opposingSides d GK := by
  euclid_finish

end Elements.Book1
