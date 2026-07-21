import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step1 (AB EF CD GK : Line) (g h k : Point)
    (hg_ab : g.onLine AB) (hg_gk : g.onLine GK)
    (hh_ef : h.onLine EF) (hh_gk : h.onLine GK)
    (hk_cd : k.onLine CD) (hk_gk : k.onLine GK)
    (hne_ef_ab : EF ≠ AB) (hne_cd_ef : CD ≠ EF)
    (hab_ef : ¬AB.intersectsLine EF) (hcd_ef : ¬CD.intersectsLine EF) :
    AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ CD.intersectsLine GK := by
  have hAB_GK : AB ≠ GK := by
    intro heq
    euclid_apply (intersection_lines_common_point h AB EF)
    euclid_finish
  have hEF_GK : EF ≠ GK := by
    intro heq
    euclid_apply (intersection_lines_common_point g AB EF)
    euclid_finish
  have hCD_GK : CD ≠ GK := by
    intro heq
    euclid_apply (intersection_lines_common_point h CD EF)
    euclid_finish
  euclid_finish

end Elements.Book1
