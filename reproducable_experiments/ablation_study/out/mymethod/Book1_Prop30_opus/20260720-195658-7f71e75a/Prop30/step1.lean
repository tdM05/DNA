import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step1 (AB CD EF GK : Line) (g h k : Point)
    (hg_AB : g.onLine AB) (hg_GK : g.onLine GK)
    (hh_EF : h.onLine EF) (hh_GK : h.onLine GK)
    (hk_CD : k.onLine CD) (hk_GK : k.onLine GK)
    (hABEF : ¬AB.intersectsLine EF) (hCDEF : ¬CD.intersectsLine EF)
    (hABCD : AB ≠ CD) (hCDEF' : CD ≠ EF) (hEFAB : EF ≠ AB) :
    AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ CD.intersectsLine GK := by
  euclid_finish

end Elements.Book1
