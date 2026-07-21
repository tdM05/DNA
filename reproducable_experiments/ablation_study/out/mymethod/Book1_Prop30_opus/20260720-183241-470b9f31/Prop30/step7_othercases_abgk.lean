import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_abgk (AB EF GK : Line) (h : Point)
  (hh_ef : h.onLine EF) (hh_gk : h.onLine GK)
  (hab_ef : ¬AB.intersectsLine EF) (hne_ef_ab : EF ≠ AB) :
  AB ≠ GK := by
  intro heq
  euclid_apply (intersection_lines_common_point h AB EF)
  euclid_finish

end Elements.Book1
