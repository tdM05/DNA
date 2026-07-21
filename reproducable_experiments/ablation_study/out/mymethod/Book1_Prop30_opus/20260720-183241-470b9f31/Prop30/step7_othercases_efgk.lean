import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_efgk (AB EF GK : Line) (g : Point)
  (hg_ab : g.onLine AB) (hg_gk : g.onLine GK)
  (hab_ef : ¬AB.intersectsLine EF) (hne_ef_ab : EF ≠ AB) :
  EF ≠ GK := by
  intro heq
  euclid_apply (intersection_lines_common_point g AB EF)
  euclid_finish

end Elements.Book1
