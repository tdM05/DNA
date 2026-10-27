import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step1 (g h k : Point) (AB CD EF GK : Line)
  (hab_ef : EF ≠ AB) (hcd_ef : CD ≠ EF)
  (hnab : ¬AB.intersectsLine EF) (hncd : ¬CD.intersectsLine EF)
  (hg_ab : g.onLine AB) (hg_gk : g.onLine GK)
  (hh_ef : h.onLine EF) (hh_gk : h.onLine GK)
  (hk_cd : k.onLine CD) (hk_gk : k.onLine GK)
  : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ CD.intersectsLine GK := by
  euclid_finish

end Elements.Book1
