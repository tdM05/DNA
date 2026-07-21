import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_ghne (AB EF : Line) (g h : Point)
  (hg_ab : g.onLine AB) (hh_ef : h.onLine EF)
  (hab_ef : ¬AB.intersectsLine EF) (hne_ef_ab : EF ≠ AB) :
  g ≠ h := by
  intro heq
  euclid_apply (intersection_lines_common_point g AB EF)
  euclid_finish

end Elements.Book1
